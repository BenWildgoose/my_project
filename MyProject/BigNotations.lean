import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

def bigO (g:ℝ → ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ (c n₀ : ℝ) , (0<c) ∧ ∀n , n₀ <= n → |f n| <= c * |g n|}


def bigOmega (g:ℝ → ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ (c n₀ : ℝ) , (0<c) ∧ ∀n , n₀ <= n → |f n| >= c * |g n|}


def bigTheta (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  { f | ∃ (c₁ c₂ n₀ : ℝ), (0 < c₁) ∧ (0 < c₂) ∧ ∀ n, n₀ ≤ n → c₁ * |g n| ≤ |f n| ∧ |f n| ≤ c₂ * |g n| }
