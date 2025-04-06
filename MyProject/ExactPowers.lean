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
    -- set l := i + 1 with hl --Replacing i+1 with l to fix type errors. Uses set
    -- have hT : T (b ^ l) = a * T (b ^ l / b) + f (b ^ l) := hT2 _ sorry --Needs completing
    -- rw [←hT]
    rw [mul_add] --Distributes the a over the two terms on the left.
    nth_rw 1 [mul_comm]
    rw [← pow_succ]


  }

  sorry
