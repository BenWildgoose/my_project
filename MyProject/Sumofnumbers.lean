import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base --This import caused a lot of issues
import Mathlib.Data.Real.Basic


-- theorem sumofn (n : ℕ) : ∑ k in Finset.range (n+1), k = n*(n+1)/2 := by
--   induction n with
--   | zero =>
--     simp
--   | succ n ih =>
--     calc
--       ∑ k in Finset.range (n + 2)
--         = ∑ k in Finset.range  (n + 1) + (n + 1) := by simp [Finset.sum_range_succ]
--       _ = n * (n + 1) / 2 + (n + 1) := by rw [ih]
--       _ = (n + 1) * (n + 2) / 2 := by ring


-- theorem sumofn (n : ℕ) : ∑ k in Finset.range (n + 1), k = n * (n + 1) / 2 := by
--   induction n with
--   | zero =>
--     simp
--   | succ n ih =>
--     rw [Finset.sum_range_succ]
--     rw [ih]
--     -- Instead of rewriting division directly, simplify without division:
--     calc
--       n * (n + 1) / 2 + (n + 1)
--         = (n * (n + 1) + 2 * (n + 1)) / 2 := by rw [← Nat.add_mul_div_left n 1 2 (by decide)]
--       _ = ((n + 1) * (n + 2)) / 2 := by ring

theorem sum_id (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2) --Get rid of division statements, they make the proof much harder.
induction' n with n ih
· simp
rw [Finset.sum_range_succ, mul_add 2, ← ih]
ring


theorem recursive_sum {f: ℕ → ℕ }
  (h₀ : f 0 = 0)
  (h₁ : ∀ n > 0, f n = f (n-1) + n) :
  ∀ n, f n = n * (n+1) / 2 :=
by
  intro n --Moves n into a local context (As seen in the first Logic and Sem lecture on Simply Typed Lambda Calc)
  -- Multiply both sides by 2 directly:
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  induction n with
  | zero =>
    simp [h₀]
  | succ n ih =>
    have hstep : f (n + 1) = f n + (n + 1) := h₁ (n + 1) (Nat.succ_pos n)
    calc
      2 * f (n + 1)
        = 2 * (f n + (n + 1)) := by rw [hstep]
      _ = 2 * f n + 2 * (n + 1) := by ring
      _ = 2 * (n * (n + 1) / 2) + 2 * (n + 1) := by rw [ih]
      _ = n * (n + 1) + 2 * (n + 1) := by
        have h := Nat.mul_div_cancel (n * (n + 1)) (by norm_num)
        rw [h]
      _ = (n + 1) * (n + 2) := by ring
--         sorry

def pos_real := { x : ℝ // 0 <= x } -- required type for T function

theorem recursive_T  {T: pos_real → pos_real}
    (h₀ : ∀ x, x < 1 → T x = 0) -- Valid way of bounding x between 0 and 1 (including 0)
    (h₁ : ∀ x, 1 ≤ x → T x = T (x / 2) + 1) :
    ∀ k ∈ ℕ, Real.log x ≤ k :=

-- Tips: Use log base 2, log₂x = lnx / ln2
-- norm_cast does something. exact mod cast does something similar (ints to reals)
-- apply? IS THE HELPER THINGY!!!
-- Talk about the lean ecosphere (problems with mathlib, Zulip, apply?).
