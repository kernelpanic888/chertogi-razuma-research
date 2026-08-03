import { redirect } from "next/navigation";

export const metadata = {
  title: "Chambers of the First Distinction · Research Lab",
  description: "A private candidate map preserving the public canon and adding new research readers.",
  robots: { index: false, follow: false },
};

export default function Home() {
  redirect("/index.html?v=research-lab-1");
}
