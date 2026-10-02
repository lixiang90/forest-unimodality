import Mathlib.Data.Rat.Defs
example (n : Nat) (q : Rat) :
    (fun i : Fin n => if i.val = 0 then q else if i.val = 1 then q else q) =
      (fun _ => q) := by
  funext i
  simp only [ite_self]
