import Lake
open Lake DSL

package «MachLib» where

-- ZERO Mathlib dependency. The independent foundations under
-- `MachLib/` are self-contained: Basic, Exp, Log, Trig, EML.
-- See `legacy_eml/` for the transitional Mathlib-dependent
-- corpus that Phase 1 ports up into MachLib.

@[default_target]
lean_lib «MachLib» where
  roots := #[`MachLib]
