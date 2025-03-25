import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O.


section basics

variable (a b : ℝ)

-- Assume `a > 0` and `b > 1` inside a context
variable (ha : 0 < a) (hb : 1 < b) --Effectively a true statement, but it will need to be called upon in proofs.

def pos_real := { x : ℝ // 0 <= x } -- required type for T function. CHANGE THIS TO >= 1???

def f (x: pos_real) : ℝ := x.val ^ 2 + 1 -- x.val lets lean know that x is from the pos_real domain.

-- def g (n : pos_real) : ℝ := ∑ a^j * f (n/(b^j)) in Finset.range (Real.logb n)

open Finset

noncomputable def g (n : pos_real) : ℝ :=
  ∑ j in Finset.range ((⌊Real.logb b n.val⌋.toNat) + 1),
    a^j * f ⟨n.val / b^j, div_nonneg n.property (pow_nonneg (le_of_lt (zero_lt_one.trans hb)) j)⟩
--g is defined as non computable as it contains logb, which could make proofs harder

-- theorem L43FirstPart (ε : ℝ)
--   ( ε > 0, f isBigO )


#check @g

end basics
