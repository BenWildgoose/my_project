import Mathlib.Tactic


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
  apply Nat.mul_ (by norm_num: 0<2)
