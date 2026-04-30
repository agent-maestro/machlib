import Hero from "@/components/Hero";
import Numbers from "@/components/Numbers";
import WhyMachLib from "@/components/WhyMachLib";
import RecordViewer from "@/components/RecordViewer";
import Engines from "@/components/Engines";
import Philosophy from "@/components/Philosophy";
import GetStarted from "@/components/GetStarted";
import Ecosystem from "@/components/Ecosystem";
import Footer from "@/components/Footer";

export default function Page() {
  return (
    <>
      <main>
        <Hero />
        <Numbers />
        <WhyMachLib />
        <RecordViewer />
        <Engines />
        <Philosophy />
        <GetStarted />
        <Ecosystem />
      </main>
      <Footer />
    </>
  );
}
