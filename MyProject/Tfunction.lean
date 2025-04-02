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

noncomputable def piecewise (x : ℝ) : ℝ :=
  if x < 0 then piecewise (x + 1) + x
  else x^2
termination_by -Int.floor x
decreasing_by
  apply Nat.lt_of_succ_le
  apply Int.floor_mono
  linarith

def T (x : ℝ) (hx : x > 0) : ℝ → ℝ :=
  if x < 1 then (fun _ => 0)
  else
    let recursive := T (x / 2) (by linarith)
    fun y => recursive y + 1
termination_by T x hx => x / 2


-- What does a case 1 T look like in the master theorem???
--Write a proof about this thing.












-- Tips: Use log base 2, log₂x = lnx / ln2
-- norm_cast does something. exact mod cast does something similar (ints to reals)
-- apply? IS THE HELPER THINGY!!!
-- Talk about the lean ecosphere (problems with mathlib, Zulip, apply?).
