import { redirect } from "next/navigation";

export const metadata = {
  title: "Why is there something rather than nothing? | Chambers of the First Distinction",
  description: "A bilingual public research map of distinction, interface, formal proof and explicit limits.",
  robots: { index: true, follow: true },
  alternates: { canonical: "https://chertogi-razuma-research.kernelpanic888.chatgpt.site/" },
};

export default function Home() {
  redirect("/index.html");
}
