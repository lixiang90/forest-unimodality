import ForestUnimodality.FreshPathContext
import ForestUnimodality.TerminalAlternateState

/-! Actual-graph soundness of terminal bridge closure. Identification of the
actual rooted block with a terminal state is an explicit structural premise;
all host means, ratio bounds, and smaller path inequalities are proved here. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u
variable {V : Type u} [DecidableEq V]

theorem IsRootedBlockAttachment.adjustedMean_pos_of_terminalState
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    (legs : List ℕ) (hl : legs ∈ terminalLegs) (b : ℕ) (hb : 1 ≤ b)
    (hne : ¬ (b = 1 ∧ (legs = [3,3] ∨ legs = [5,3])))
    (hstate : actualBlockState G T w = castState (bridgeState legs b)) :
    0 < adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) := by
  have hc : (H ∪ T).card = H.card + T.card := card_union_of_disjoint h.disjoint
  have hT : 0 < T.card := card_pos.mpr ⟨w, h.block_root_mem⟩
  have hH := hsmaller V G H (by omega) hG
  have hJ := hsmaller V G (H.erase v)
    (lt_of_le_of_lt (card_le_card (erase_subset _ _)) (by omega)) hG
  let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
  let X := r * adjustedMeanPotential G H (independenceNumberOn G H)
  let Y := adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))
  let d : ℝ := rootDefect G H v
  have hr := partitionFunction_delete_ratio_bounds G H h.host_root_mem (z := (2 : ℝ))
    (by norm_num)
  have hrlo : 1 ≤ r := hr.1
  have hrhi : r ≤ 3 := by simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hr.2
  have hX : 0 ≤ X := mul_nonneg (by dsimp only [r]; linarith [hr.1]) hH
  have hY : 0 ≤ Y := hJ
  have hd : d = 0 ∨ d = 1 := by
    rcases rootDefect_zero_or_one G H v with he | he <;> simp [d, he]
  have hpath : ∀ j : ℕ, 0 < j → (j : ℝ) < (castState (bridgeState legs b)).N →
      0 ≤ E (castState (TerminalContextCertificate.pathState j)) d X Y r := by
    intro j hj hjN
    rw [← hstate] at hjN
    change (j : ℝ) < (T.card : ℝ) at hjN
    have hjT : j < T.card := by exact_mod_cast hjN
    exact FreshPathContext.path_residual_nonneg hsmaller G hG H h.host_root_mem
      j hj (by omega)
  apply h.adjustedMean_pos_iff.mpr
  rw [hstate]
  change 0 < E (castState (bridgeState legs b)) d X Y r
  by_cases hs : b ≤ 24
  · exact TerminalAlternateState.short_bridge_all_states_positive
      legs hl b hb hs hne d X Y r hd hX hY hrlo hrhi hpath
  · exact long_bridge_all_states_positive legs hl b (by omega) d X Y r hd hX hY hrlo hrhi

#print axioms IsRootedBlockAttachment.adjustedMean_pos_of_terminalState
end ForestUnimodality
