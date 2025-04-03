import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O. NOW USING MY OWN DEFINITION
--import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real --Loads of stuff for dealing with powers.

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
  unfold bigO --Unfolding the full definition of bigO. This gives a definition of bigO with quantifiers.
  simp
  simp at hf --Very simple tactic that just tries to simplify whatever is in the target ⊢. Extremely useful
  match hf with
  | ⟨k, hk⟩ => --Here we match a term, k, with a ∃ statement (EXISTENSIALS).
  --k has replaced c within the hypotheses hf.
    exists k --k exists now.
    constructor --Splits the and statement in half.
    exact hk.1 --Goal is to prove 0 < k , which comes for free from hk.
    match hk.2 with --Same process as before.
    | ⟨N, hN⟩ => --Putting N where k is.
    exists N*b --x is replaced with N*b.
    intro n --We have a '∀ n' at the start of ⊢, so introducing n gets this sorted.
    intro M --M takes the place of N * b ≤ n.
    apply hN --The statement ⊢ |f (n / b)| ≤ k * g (n / b) is proven, but Lean needs to see that N <= n/b.
    refine (le_div_iff₀' ?_).mpr ?_ --Tactic from apply?, now just needs to see b > 0.
    linarith
    linarith --Usually deals with simple inequalities.
    sorry

lemma Stuff  (b a ε n: ℝ ) (hb : b > 1) (he : 0 < ε) (ha : 0 < a) (hn : n >= 0) :
  ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
    (a^j * (n/b^j)^(Real.logb b a - ε) ) = n^(Real.logb b a - ε) * ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
      (a*(b^ε) / b^(Real.logb b a))^j := by
      field_simp
      rw [Finset.mul_sum]
      congr --This thing is very useful
      funext j
      field_simp
      rw [Real.div_rpow]
      field_simp
      nth_rw 1 [mul_assoc, mul_comm]
      rw [mul_assoc, mul_assoc]
      simp
      left
      ring_nf
      rw [mul_comm, mul_assoc]
      simp
      left
      ring_nf
      rw [← Real.rpow_natCast, ← Real.rpow_mul] --j is inside the bracket
      --Naturals are an inductive type (zero and succ). Integers in a different way. Reals are cauchy.
      rw [← Real.rpow_natCast, ← Real.rpow_mul] --Repeating puts the next power of j inside the bracket.
      nth_rw 2 [mul_comm]
      group --Swaps j and ε in final bit. Also turns j into ↑j ? Probably worth doing to get rid of standalone j.
      rw [Real.rpow_sub]
      nth_rw 2 [Real.rpow_mul]
      rw [div_mul_eq_mul_div]
      --ring
      field_simp
      rw [← Real.rpow_natCast, ← Real.rpow_mul, mul_comm] --This solves the main goal.
      repeat linarith
      apply pow_pos --Got rid of all the goals with powers in. Apart from the one with just j in.
      nlinarith --Gets rid of b > 0 for some reason. Does not do this for b >= 0?
      exact le_of_lt (zero_lt_one.trans hb)
      exact le_of_lt (zero_lt_one.trans hb) --Finally solves b >= 0.
      apply hn --Gets rid of n >= 0.
      exact pow_nonneg (le_of_lt (zero_lt_one.trans hb)) j --Solves at 0 >= b^j.




      --apply le_of_lt





theorem Case1_3 (g : ℝ → ℝ ) (b a ε: ℝ ) (hb : b > 1) (he : 0 < ε) (ha : 0 < a)
  (hf : (fun n => f (n) ) ∈ bigO (fun n => ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
  (a^j * (n/b^j)^(Real.logb b a - ε) ))):
  (fun n => f (n) ) ∈ bigO (fun n => n^(Real.logb b a - ε) * ∑ j in Finset.range ((⌊Real.logb b n⌋.toNat)),
    (a*b^ε / b^(Real.logb b a))^j) := by
    unfold bigO
    unfold bigO at hf
    simp
    simp at hf
    match hf with
    | ⟨k,hk⟩ =>
    exists k
    constructor
    exact hk.1
    match hk.2 with
    | ⟨r, hr⟩ =>
    exists r --This could renamed in all sorts of ways. Question is what value would make the proof easy.
    intro n --Value of...
    intro hn












    sorry




end basics
