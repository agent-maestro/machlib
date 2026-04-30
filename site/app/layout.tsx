import type { Metadata } from "next";
import "./globals.css";

const SITE_URL = "https://machlib.org";

export const metadata: Metadata = {
  metadataBase: new URL(SITE_URL),
  title: "MachLib — For machines, by machines",
  description:
    "Machine-native formal mathematics. 449 records. 4.77s build. Zero Mathlib dependency.",
  applicationName: "MachLib",
  authors: [{ name: "Mosa Creates LLC" }],
  keywords: [
    "MachLib",
    "Lean 4",
    "formal mathematics",
    "machine learning",
    "theorem proving",
    "EML",
    "Monogate",
    "agent-native",
  ],
  openGraph: {
    type: "website",
    url: SITE_URL,
    title: "MachLib — For machines, by machines",
    description:
      "Machine-native formal mathematics. 449 records. 4.77s build. Zero Mathlib dependency.",
    siteName: "MachLib",
  },
  twitter: {
    card: "summary_large_image",
    title: "MachLib — For machines, by machines",
    description:
      "Machine-native formal mathematics. 449 records. 4.77s build. Zero Mathlib dependency.",
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
