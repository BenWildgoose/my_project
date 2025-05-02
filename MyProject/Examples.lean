import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O. NOW USING MY OWN DEFINITION
--import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real --Loads of stuff for dealing with powers.


example (x : ℝ) : (x > 1) → (2 * x > 2) := by
intro h
linarith


variable (P : ℕ → Prop)

example : (∀ k, P k) := by
  intro k
  induction k with
  | zero => sorry
  | succ i hi => sorry


theorem example3 : (∃k , 2 * k = 4) := by
  exists 2


example (n : ℕ ) (h1 : n > 0) : ∃ m : ℕ , n = m + 1 := by
  exists (n - 1)
  match n with
    | 0   => contradiction
    | n'+1 =>
      rfl


example (n : ℕ) (h : ∃ k, n = 2 * k) : ∃ j, n + 2 = 2 * j := by
  match h with
  | ⟨k, hk⟩ =>
    -- We know n = 2 * k
    -- Let's propose k' = k + 1
    exists (k + 1)
    linarith
