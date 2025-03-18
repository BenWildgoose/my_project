import Mathlib



def PosReal := {x : ℝ // 0 < x}

def T : PosReal → PosReal
| ⟨x,h⟩ =>
  if x < 1 then ⟨1, by norm_num⟩ --Proves that 0<1
  else ⟨(T ⟨x / 2, by linarith⟩).1 + 1, by
    have h₂ : x / 2 > 0 := by linarith
    -- exact add_pos (T ⟨x / 2 , h₂⟩).2 zero_lt_one⟩
-- termination_by T x => Nat.floor x
-- decreasing_by simp_wf
