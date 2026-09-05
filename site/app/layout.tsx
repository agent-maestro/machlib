import type { Metadata } from "next";
import "./globals.css";

const SITE_URL = "https://machlib.org";

export const metadata: Metadata = {
  metadataBase: new URL(SITE_URL),
  title: "MachLib — machine-checked theorems about compiled numerics",
  description:
    "A Mathlib-free Lean 4 library that proves things about EML kernels, the exp/log expression language Forge compiles to C, GPU code and RTL. Every axiom listed and modeled; every claim paired with the command that checks it.",
  applicationName: "MachLib",
  authors: [{ name: "Mosa Creates LLC" }],
  keywords: [
    "MachLib",
    "Lean 4",
    "formal verification",
    "verified numerics",
    "floating-point error",
    "fixed-point",
    "Khovanskii",
    "EML",
    "Monogate",
  ],
  openGraph: {
    type: "website",
    url: SITE_URL,
    title: "MachLib — machine-checked theorems about compiled numerics",
    description:
      "A Mathlib-free Lean 4 library that proves things about EML kernels. Every axiom listed and modeled; every claim paired with the command that checks it.",
    siteName: "MachLib",
  },
  twitter: {
    card: "summary_large_image",
    title: "MachLib — machine-checked theorems about compiled numerics",
    description:
      "A Mathlib-free Lean 4 library that proves things about EML kernels. Every axiom listed and modeled; every claim paired with the command that checks it.",
  },
  robots: { index: true, follow: true },
  icons: { icon: "/favicon.ico" },
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
