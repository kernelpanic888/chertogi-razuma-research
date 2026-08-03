/** Cloudflare Worker entry point for the vinext-starter template. */
import { handleImageOptimization, DEFAULT_DEVICE_SIZES, DEFAULT_IMAGE_SIZES } from "vinext/server/image-optimization";
import handler from "vinext/server/app-router-entry";
import { incrementPageViews, readPageViews } from "../db/visit-counter";

interface Env {
  ASSETS: Fetcher;
  DB: D1Database;
  COUNTER_READ_TOKEN?: string;
  IMAGES: {
    input(stream: ReadableStream): {
      transform(options: Record<string, unknown>): {
        output(options: { format: string; quality: number }): Promise<{ response(): Response }>;
      };
    };
  };
}

function sameToken(actual: string, expected: string | undefined): boolean {
  if (!expected || actual.length !== expected.length) return false;
  let difference = 0;
  for (let index = 0; index < actual.length; index += 1) {
    difference |= actual.charCodeAt(index) ^ expected.charCodeAt(index);
  }
  return difference === 0;
}

interface ExecutionContext {
  waitUntil(promise: Promise<unknown>): void;
  passThroughOnException(): void;
}

// Image security config. SVG sources with .svg extension auto-skip the
// optimization endpoint on the client side (served directly, no proxy).
// To route SVGs through the optimizer (with security headers), set
// dangerouslyAllowSVG: true in next.config.js and uncomment below:
// const imageConfig: ImageConfig = { dangerouslyAllowSVG: true };

const worker = {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);

    if (url.pathname === "/_internal/page-views") {
      const authorization = request.headers.get("Authorization") ?? "";
      const token = authorization.startsWith("Bearer ")
        ? authorization.slice("Bearer ".length)
        : "";

      if (request.method !== "GET" || !sameToken(token, env.COUNTER_READ_TOKEN)) {
        return new Response("Not Found", {
          status: 404,
          headers: { "Cache-Control": "no-store" },
        });
      }

      const pageViews = await readPageViews(env.DB);
      return Response.json(
        { page_views: pageViews },
        {
          headers: {
            "Cache-Control": "no-store",
            "X-Robots-Tag": "noindex, nofollow, noarchive",
          },
        },
      );
    }

    if (url.pathname === "/_vinext/image") {
      const allowedWidths = [...DEFAULT_DEVICE_SIZES, ...DEFAULT_IMAGE_SIZES];
      return handleImageOptimization(request, {
        fetchAsset: (path) => env.ASSETS.fetch(new Request(new URL(path, request.url))),
        transformImage: async (body, { width, format, quality }) => {
          const result = await env.IMAGES.input(body).transform(width > 0 ? { width } : {}).output({ format, quality });
          return result.response();
        },
      }, allowedWidths);
    }

const servesCanonicalPage =
  request.method === "GET" &&
  (url.pathname === "/" || url.pathname === "/index.html") &&
  (request.headers.get("Accept") ?? "").includes("text/html");

if (!servesCanonicalPage) {
  return handler.fetch(request, env, ctx);
}

const canonicalAssetUrl = new URL("/_canonical/page.dat", request.url);
const response = await env.ASSETS.fetch(new Request(canonicalAssetUrl, request));

if (!response.ok) {
  return response;
}

let counterStatus = "recorded";
try {
  await incrementPageViews(env.DB);
} catch {
  counterStatus = "unavailable";
}

const headers = new Headers(response.headers);
headers.set("Content-Type", "text/html; charset=utf-8");
headers.set("X-Chertogi-Counter", counterStatus);

return new Response(response.body, {
  status: response.status,
  statusText: response.statusText,
  headers,
});
  },
};

export default worker;
