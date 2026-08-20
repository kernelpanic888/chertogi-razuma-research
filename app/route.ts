import homeHtml from "../public/index.html?raw";

export const dynamic = "force-static";
export const corpusRelease = "first-distinction-53";
const canonicalUrl = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/";

export function GET() {
  return new Response(homeHtml, {
    headers: {
      "content-type": "text/html; charset=utf-8",
      "cache-control": "public, max-age=0, must-revalidate",
      "x-robots-tag": "index, follow, max-image-preview:large",
      link: `<${canonicalUrl}>; rel="canonical"`,
    },
  });
}
