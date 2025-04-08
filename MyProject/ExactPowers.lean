import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O. NOW USING MY OWN DEFINITION
--import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real --Loads of stuff for dealing with powers.


-- def T (a : ℝ) (f : ℝ → ℝ) (b : ℕ) (hb : 1 < b) : ℝ → ℝ
--   | 1 => 1
--   | n => if n < b then f n else a * T a f b hb (n / b) + f n
--   decreasing_by


theorem exactPowersOfb (T : ℝ → ℝ) (f: ℝ → ℝ ) (hb : b > 1) (hT1 : ∀ x , x <= 1 → T x = 1 )
(hT2 : ∀ x , x > 1 → T x = a *  T (x / b) + f x) :
  T (b ^ k) = a^k + ∑ j in Finset.range (k), (a^j * f ((b^k) / (b^j)) ) := by
  induction k with
  | zero => simp
            apply hT1
            simp
  | succ i ih => {
    rw [hT2]
    have h : b ^ (i + 1) / b = b * b ^ i * b⁻¹ := by ring
    rw [h]
    nth_rw 3 [mul_comm]
    field_simp
    rw [ih]
    --Using ring tactic causes issues (turns instances of j into x).
    -- set l := i + 1 with hl --Replacing i+1 with l to fix type errors. Uses set
    -- have hT : T (b ^ l) = a * T (b ^ l / b) + f (b ^ l) := hT2 _ sorry --Needs completing
    -- rw [←hT]
    rw [mul_add] --Distributes the a over the two terms on the left.
    nth_rw 1 [mul_comm]
    rw [← pow_succ]
    --Having trouble cancelling out the a ^ (i + 1) from each side.
    --They both have unusual types that don't work very well.
    rw [add_assoc]
    simp --This and above line removes the a ^ (i + 1) from either side.
    rw [Finset.mul_sum] --Renames j to i_1 to avoid capture... Will be a problem later in the proof.
    rw [Finset.sum_range_succ'] --Notice this tactic has a ' at the end. It peels off the first term, instead of the last.
    simp --Gets rid of the nasty function f (b ^ (i+1))
    congr
    funext i_1 --Used for showing two functions are equal.
    rw [← mul_assoc]
    rw [pow_succ]
    nth_rw 2 [mul_comm]
    field_simp --Gets rid of the a * a^i_1
    constructor --field_simp left an ∨, so constructor allows us to focus only on the first bit.
    rw [pow_succ]
    rw [pow_succ]
    ring_nf
    field_simp

    --Now starts proof of substatement.
    --ring_nf
    rw [← Real.rpow_natCast] --Turns the problem into ℝ ^ ℝ instead of ℝ ^ ℕ
    apply Real.one_lt_rpow hb
    positivity

    -- induction i with
    -- | zero => {
    --   simp
    --   apply hb
    -- }
    -- | succ m mh => {
    --   rw [pow_succ]
    --   nth_rw 2 [mul_comm]
    --   have hb' : b>0 := by apply lt_trans zero_lt_one hb
    --   have mh' : b * b ^ m > 0 := by apply lt_trans zero_lt_one mh


    -- }



    --rw [h₂]



    --have b_ne_zero : b ≠ 0 := ne_of_gt hb


    --rw [← mul_assoc]





  }

  sorry

theorem Case2Exact (k : ℕ ) (T : ℝ → ℝ) (f: ℝ → ℝ ) (hb : b > 1) (hT1 : ∀ x , x <= 1 → T x = 1 )
(hT2 : ∀ x , x > 1 → T x = a *  T (x / b) + f x) (hf : ∀x, f x = x ^ (Real.logb b a)) :
  T (b^k) = a^k * (1 + k) := by
  rw [exactPowersOfb T f hb hT1 hT2]
  ring_nf
  rw [mul_add]
  simp
  have moreSums : ∑ j ∈ Finset.range k, a ^ j * f (b ^ k / b ^ j) = ∑ j ∈ Finset.range k, a^k := by {
    congr
    funext m
    rw [hf]
    ring_nf
    rw [Real.mul_rpow]
    rw [← Real.rpow_natCast] --repeat didnt work here
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    rw [← Real.rpow_mul]
    nth_rw 3 [mul_comm]
    nth_rw 4 [mul_comm]
    rw [Real.rpow_mul]
    rw [Real.rpow_mul]
    rw [Real.rpow_logb]
    rw [Real.inv_rpow]
    rw [Real.rpow_logb]
    field_simp
    ring_nf
    simp
    nth_rw 2 [mul_comm]
    nth_rw 1 [mul_assoc]
    field_simp
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [mul_div_cancel_of_invertible]

  }
  -- rw [hf]
