/** @type {import('next').NextConfig} */
const nextConfig = {
  reactStrictMode: true,
  poweredByHeader: false,
  output: "export",              // static export for Cloudflare Pages (free builds + CDN)
  images: { unoptimized: true }, // no Vercel image optimizer on static export
};

export default nextConfig;
