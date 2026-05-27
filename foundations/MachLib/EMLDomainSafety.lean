import MachLib.Exp

/-!
# EML domain-safety footholds

Tiny checked witnesses used by Monogate's EML packet-review loop.
These are deliberately narrow: they discharge one local domain fact
without claiming complete EML safety, compiler correctness, or rewrite
soundness.
-/

namespace MachLib
namespace Real

/-- Sum of two positive reals is positive, derived from MachLib's order axioms. -/
theorem add_pos {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have hba : b < b + a := by
    have h := add_lt_add_left ha b
    rw [add_zero] at h
    exact h
  have h0ba : 0 < b + a := lt_trans_ax hb hba
  rw [add_comm] at h0ba
  exact h0ba

/-- Checked witness for the EML-R8 softplus/log-sum-exp packet:
`ln(exp(a) + exp(b))` has a positive log argument. -/
theorem softplus_pair_log_argument_positive (a b : Real) :
    0 < exp a + exp b :=
  add_pos (exp_pos a) (exp_pos b)

end Real
end MachLib

