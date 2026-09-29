import ForestUnimodality.ForestLeaf
import ForestUnimodality.GraphBounds
import Mathlib.Data.Nat.Choose.Basic

/-! A forest has at least as many independent k-sets as a path of the same
order. The upper argument `S.card + 1 - k` intentionally handles the empty
graph and all out-of-support degrees before natural subtraction truncates. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The path coefficient lower bound, for every finite induced forest and k. -/
theorem choose_path_le_countIndependent (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (k : ℕ) :
    Nat.choose (S.card + 1 - k) k ≤ countIndependent G S k := by
  classical
  revert k
  refine S.strongInductionOn ?_
  intro S ih k
  cases k with
    | zero => simp
    | succ k =>
      by_cases hn : k + 1 ≤ S.card
      · have hS : S.Nonempty := card_pos.mp (by omega)
        obtain ⟨v, hv, hsmall⟩ := exists_closedNeighborhoodIn_card_le_two G hG S hS
        have hclosed : closedNeighborhoodIn G S v ⊆ S := by
          unfold closedNeighborhoodIn
          exact filter_subset _ _
        have hvclosed : v ∈ closedNeighborhoodIn G S v := by
          simp [closedNeighborhoodIn, hv]
        have hleft := ih (S.erase v) (erase_ssubset hv) (k+1)
        have hright := ih (S \ closedNeighborhoodIn G S v)
          (sdiff_ssubset hclosed ⟨v, hvclosed⟩) k
        have hcardleft := card_erase_add_one hv
        have hcardright := card_sdiff_add_card_eq_card hclosed
        have hmono : Nat.choose (S.card - k - 1) k ≤
            Nat.choose ((S \ closedNeighborhoodIn G S v).card + 1 - k) k :=
          Nat.choose_le_choose k (by omega)
        have hlower : Nat.choose (S.card - k - 1) k ≤
            countIndependent G (S \ closedNeighborhoodIn G S v) k := hmono.trans hright
        have hupper : Nat.choose (S.card - k - 1) (k+1) ≤
            countIndependent G (S.erase v) (k+1) := by
          convert hleft using 1 <;> congr 1 <;> omega
        rw [countIndependent_succ_delete_vertex G S hv k]
        have hnumer : S.card + 1 - (k+1) = (S.card - k - 1) + 1 := by omega
        rw [hnumer, Nat.choose_succ_succ']
        exact (Nat.add_le_add hlower hupper).trans_eq (Nat.add_comm _ _)
      · rw [Nat.choose_eq_zero_of_lt (show S.card + 1 - (k+1) < k+1 by omega)]
        exact Nat.zero_le _

#print axioms choose_path_le_countIndependent

end ForestUnimodality
