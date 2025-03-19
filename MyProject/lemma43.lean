import Mathlib.Analysis.Asymptotics.Asymptotics

open Asymptotics

variable {a b : ℝ} (f : ℝ → ℝ)

noncomputable def g (n : ℝ) : ℝ :=
  ∑ j in Finset.range (Int.floor (Real.logb b n) + 1),
    a ^ j * f (n / b ^ j)

theorem asymptotic_behavior_case1
  (h₁ : ∃ ε > 0, ∀ n ≥ 1, f n ≤ n ^ (Real.logb b a - ε)) :
  g f n =O[⊤] (λ n, n ^ (Real.logb b a)) := sorry

theorem asymptotic_behavior_case2
  (k : ℝ)
  (h₂ : ∃ c > 0, ∃ C > 0, ∀ n ≥ 1, c * n ^ (Real.logb b a) * (Real.log n) ^ k ≤ f n ∧
    f n ≤ C * n ^ (Real.logb b a) * (Real.log n) ^ k) :
  g f n =Θ[⊤] (λ n, n ^ (Real.logb b a) * (Real.log n) ^ (k + 1)) := sorry

theorem asymptotic_behavior_case3
  (h₃ : ∃ c, 0 < c ∧ c < 1 ∧ ∀ n ≥ 1, 0 < a * f (n / b) ∧ a * f (n / b) ≤ c * f n) :
  g f n =Θ[⊤] f := sorry
