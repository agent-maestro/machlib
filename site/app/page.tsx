import Hero from "@/components/Hero";
import Numbers from "@/components/Numbers";
import Lanes from "@/components/Lanes";
import TrustBase from "@/components/TrustBase";
import CheckIt from "@/components/CheckIt";
import NotClaimed from "@/components/NotClaimed";
import Ecosystem from "@/components/Ecosystem";
import Footer from "@/components/Footer";

export default function Page() {
  return (
    <>
      <main>
        <Hero />
        <Numbers />
        <Lanes />
        <TrustBase />
        <CheckIt />
        <NotClaimed />
        <Ecosystem />
      </main>
      <Footer />
    </>
  );
}
