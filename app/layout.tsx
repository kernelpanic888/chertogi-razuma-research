import type { Metadata } from "next";
import "./globals.css";

const canonicalUrl = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/";
const socialImage = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/og-first-distinction-v1.png";

export const metadata: Metadata = {
  metadataBase: new URL(canonicalUrl),
  title: "Chambers of the First Distinction",
  description: "A public research map of distinction, interface and return.",
  authors: [{ name: "Aleksey Salkutsan", url: "https://orcid.org/0009-0006-8717-0492" }],
  alternates: {
    canonical: canonicalUrl,
    languages: { en: canonicalUrl, ru: canonicalUrl },
  },
  robots: {
    index: true,
    follow: true,
    googleBot: { index: true, follow: true, "max-image-preview": "large" },
  },
  icons: { icon: "/favicon.svg", shortcut: "/favicon.svg" },
  openGraph: {
    title: "Chambers of the First Distinction",
    description: "A public research map of distinction, interface and return.",
    url: canonicalUrl,
    siteName: "Chambers of the First Distinction",
    type: "website",
    locale: "en_US",
    alternateLocale: ["ru_RU"],
    images: [{ url: socialImage, width: 1200, height: 630, alt: "Chambers of the First Distinction research map" }],
  },
  twitter: {
    card: "summary_large_image",
    title: "Chambers of the First Distinction",
    description: "A public research map of distinction, interface and return.",
    images: [socialImage],
  },
};

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return <html lang="en"><body>{children}</body></html>;
}
