import type { Metadata } from "next";
import "./globals.css";

const SITE_URL = "https://machlib.org";

export const metadata: Metadata = {
  metadataBase: new URL(SITE_URL),
  title: "MachLib — For machines, by machines",
  description:
    "Machine-native formal-library corpus workbench with zero Mathlib dependency in the current public default tree and release target.",
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
      "Machine-native formal-library corpus workbench with zero Mathlib dependency in the current public default tree and release target.",
    siteName: "MachLib",
  },
  twitter: {
    card: "summary_large_image",
    title: "MachLib — For machines, by machines",
    description:
      "Machine-native formal-library corpus workbench with zero Mathlib dependency in the current public default tree and release target.",
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
