import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O. NOW USING MY OWN DEFINITION


section basics

open Asymptotics Filter Real

variable (a b ε: ℝ)

-- Assume `a > 0` and `b > 1` inside a context
variable (ha : 0 < a) (hb : 1 < b) (he : 0 < ε) --Effectively a true statement, but it will need to be called upon in proofs.

def pos_real := { x : ℝ // 1 <= x } -- required type for T function. CHANGE THIS TO >= 1???

variable (f : ℝ → ℝ)-- Currently using f: ℝ → ℝ . This MIGHT cause some small issues.

variable (h0 : f =O[Filter.atTop] fun n => n^(Real.logb b (a-ε))) --atTop is a filter that represents limit to infinity, on an ordered set.
-- This variable is h0, NOT hO.

open Finset

noncomputable def g (n: pos_real) : ℝ :=
  ∑ j in Finset.range ((⌊Real.logb b n.val⌋.toNat) + 1),
    a^j * f (n.val / b^j)

-- g is defined as non computable as it contains logb, which could make proofs harder
-- Use g as a function from ℝ → ℝ . Then just say 'I only care about n>= 1' Same for f?

-- Substituting n/b^j for the given big O value of f(n).
theorem Case1_0 (j : ℕ) (hO : f =O[Filter.atTop] (fun n => n^(Real.logb b (a) - ε))) :
  (fun n => f (n / b^j)) =O[Filter.atTop] (fun n => (n / b^j)^(Real.logb b (a) - ε)) := by
  rw [Asymptotics.isBigO_iff] at hO ⊢
  match hO with
  | ⟨k, hk⟩ =>
    exists k*b^j
    intros
    sorry
  -- refine isBigO_iff.mp ?_
  -- refine IsBigO.of_abs_abs ?_
  -- refine IsBigO.abs_abs ?_
  -- apply?


  sorry

-- Using the definition of g(n) and subbing in the big O value of f. This is a bit of a problem as big O is a set of values.
-- theorem Case1_1 (j : ℕ ) :

-- The sum is moved into the big O notation.
-- theorem Case 1_2


--The power ^(logb(a-ε) is distributed over n/b^j). The part with n^(...) is moved out of the sum too.
-- theorem Case1_3 :
--   (g =O[atTop] fun n =>
--     ∑ j in range (⌊Real.logb b n⌋.toNat + 1), a^j * (n / b^j)^(Real.logb b (a - ε))) →
--   (g =O[atTop] fun n =>
--     n^(Real.logb b (a - ε)) * ∑ j in range (⌊Real.logb b n⌋.toNat + 1), (a * b^ε / b^(Real.logb b a))^j) := by
--   sorry


--Use the definition of logarithms to cancel out the a/b^(logb b a).
--theorem Case1_4


--Use the definition of a geometric sum to remove the ∑.
--theorem Case1_5


--Remove the denominator b^ε -1 as it is a constant that won't affect bounds.
--theorem Case1_6

--Some substition required to achieve the result of O(n^(logb b a))
--theorem Case1_7

def bigO (g:ℝ → ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ (c n₀ : ℝ) , (0<c) ∧ ∀n , n₀ <= n → |f n| <= c * g n}

theorem Substitution (g : ℝ → ℝ) (hf: f ∈ bigO g) (b : ℝ) (hb : b > 1):
  (fun n => f (n / b)) ∈ bigO (fun n => g (n / b)) := by
  unfold bigO at hf
  unfold bigO
  simp
  simp at hf
  match hf with
  | ⟨k, hk⟩ =>
    exists k
    constructor
    exact hk.1
    match hk.2 with
    | ⟨N, hN⟩ =>
    exists N*b
    intro n
    intro M
    apply hN
    refine (le_div_iff₀' ?_).mpr ?_
    linarith
    linarith

theorem Case1_3 (g : ℝ → ℝ ) (b a ε: ℝ ) (hb : b > 1) (he : 0 < ε) (ha : 0 < a)
  (hf : (fun n => f (n) ) ∈ bigO (fun n => ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
  (a^j * (n/b^j)^(Real.logb b a - ε) ))):
  (fun n => f (n) ) ∈ bigO (fun n => n^(Real.logb b a - ε) * ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
    (a*b^ε / b^(Real.logb b a))^j) := by

    sorry




end basics
