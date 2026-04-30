import MachLib.EML

-- Fully-qualified — works without `open`.
#check @MachLib.Real.exp
#check @MachLib.Real.log
#check @MachLib.Real.eml

-- Unqualified — works after `open`.
open MachLib.Real
#check @eml
#check @exp
