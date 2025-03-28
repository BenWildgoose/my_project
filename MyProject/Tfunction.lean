import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O.

def pos_real := { x : ℝ // 0 <= x } -- required type for T function

-- variable (a b : ℝ)

variable (f : ℝ → ℝ)

variable (b : ℝ)

def φ : ℕ → ℕ
  | 0 => 0
  | x+1 => x

-- def T : ℝ → ℝ
--   | x <= 1 => 0
--   | x > 1 => T (x / b) + 1

noncomputable def T (n b : ℝ) : ℕ :=
  if n < b then 1 else T (n / b) b + 1
  termination_by T n b => ⌊log b n⌋
  decreasing_by
    simp only [log_div_base, log_self]
    apply Nat.floor_lt; linarith











-- Tips: Use log base 2, log₂x = lnx / ln2
-- norm_cast does something. exact mod cast does something similar (ints to reals)
-- apply? IS THE HELPER THINGY!!!
-- Talk about the lean ecosphere (problems with mathlib, Zulip, apply?).
