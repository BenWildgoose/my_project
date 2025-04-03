import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base --For using log base b
import Mathlib.Analysis.Asymptotics.Defs -- Contains the definitions for big-O. NOW USING MY OWN DEFINITION
--import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real --Loads of stuff for dealing with powers.


def T (a b n : ℝ) (f : ℝ → ℝ) (k : ℕ ) :
