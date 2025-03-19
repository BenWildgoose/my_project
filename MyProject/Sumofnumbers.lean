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


theorem sumofn (n : ℕ) : ∑ k in Finset.range (n + 1), k = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    ring_nf
    rw [(by ring_nf: 1 + n = (2 + 2*n)/2)]
