import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base --This import caused a lot of issues
import Mathlib.Data.Real.Basic

def pos_real := { x : ℝ // 0 <= x } -- required type for T function

theorem recursive_T  {T : pos_real → pos_real}
    (h₀ : ∀ x : pos_real, x.val < 1 → T x = ⟨0, by norm_num⟩) -- Valid way of bounding x between 0 and 1 (including 0)
    (h₁ : ∀ x : pos_real, 1 ≤ x.val → T x = ⟨T ⟨x.val / 2, by positivity⟩.val + 1, by positivity⟩) :
    ∀ (x : pos_real), ∃ k : ℕ, Real.log2 x.val ≤ k :=


-- Tips: Use log base 2, log₂x = lnx / ln2
-- norm_cast does something. exact mod cast does something similar (ints to reals)
-- apply? IS THE HELPER THINGY!!!
-- Talk about the lean ecosphere (problems with mathlib, Zulip, apply?).
