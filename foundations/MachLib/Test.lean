import MachLib.EML
import MachLib.Trig

-- Fully-qualified — works without `open`.
#check @MachLib.Real.exp
#check @MachLib.Real.log
#check @MachLib.Real.eml
#check @MachLib.Real.tanh
#check @MachLib.Real.sqrt
#check @MachLib.Real.atan2
#check @MachLib.Real.arcsin
#check @MachLib.Real.arccos

-- Unqualified — works after `open`.
open MachLib.Real
#check @eml
#check @exp
#check @tanh
#check @sqrt
#check @atan2
