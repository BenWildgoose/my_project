-- First define the theorem (Lemma 4.2) so that it is set up for proving.
-- def T : ℝ → ℝ
--   | 0 <= < 1 => --Big theta of 1 (constant rate of change)
--   | 1 <= => a

def search {α} (f : Nat → Option α) (start : Nat) : Option α :=
  match f start with
  | .some x => .some x
  | .none =>
    match start with
    | 0 => .none
    | n+1 => search f n

theorem search_const_none {α} (start : Nat) :
    search (α := α) (fun _ => .none) start = .none := by
  induction start
  case zero => rfl
  case succ _n IH => exact IH




def searchWFR {α} (f : Nat -> Option α) (start : Nat) (to : Nat) : Option α :=
  match f start with
  | .some x => .some x
  | .none =>
    if start < to then
      searchWFR f (start + 1) to
    else
      .none
termination_by to - start --This function is using well-founded recursion since termination_by is used
