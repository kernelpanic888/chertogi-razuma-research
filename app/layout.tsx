import type { Metadata } from "next";
import "./globals.css";

const socialImage = "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/og-first-distinction-v1.png";

export const metadata: Metadata = {
  title: "Chambers of the First Distinction",
  description: "A public research map of distinction, interface and return.",
  robots: { index: true, follow: true },
  icons: { icon: "/favicon.svg", shortcut: "/favicon.svg" },
  openGraph: {
    title: "Chambers of the First Distinction",
    description: "A public research map of distinction, interface and return.",
    url: "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/",
    siteName: "Chambers of the First Distinction",
    type: "website",
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
