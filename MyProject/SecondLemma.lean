import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O.


section basics

variable (a b ε: ℝ)

-- Assume `a > 0` and `b > 1` inside a context
variable (ha : 0 < a) (hb : 1 < b) (he : 0 < ε) --Effectively a true statement, but it will need to be called upon in proofs.

def pos_real := { x : ℝ // 1 <= x } -- required type for T function. CHANGE THIS TO >= 1???

variable (f : ℝ → ℝ)-- Currently using f: ℝ → ℝ . This MIGHT cause some small issues.

-- def g (n : pos_real) : ℝ := ∑ a^j * f (n/(b^j)) in Finset.range (Real.logb n)

open Finset

noncomputable def g (n: pos_real) : ℝ :=
  ∑ j in Finset.range ((⌊Real.logb b n.val⌋.toNat) + 1),
    a^j * f (n.val / b^j)


-- g is defined as non computable as it contains logb, which could make proofs harder
-- Use g as a function from ℝ → ℝ . Then just say 'I only care about n>= 1' Same for f?






#check @g

end basics
