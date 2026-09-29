import ForestUnimodality.PenultimateSeed
import ForestUnimodality.AttachmentComponent
import ForestUnimodality.TreeFanHostSplit

/-! Complete actual eight-type fan construction around the penultimate
branching vertex of a hypothetical smallest negative forest. -/
namespace ForestUnimodality
open Finset SimpleGraph
universe u
variable {V : Type u} [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem IsPenultimateSeed.adjustedMean_pos
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S : Finset V} {r v c : V} {H T : Finset V}
    (h : IsPenultimateSeed G S r v c H T) (hconn : (G.induce (S : Set V)).Connected)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  classical
  rcases h with ⟨hS, hrH, _, hatt, hterm, hvdeg, _, hbound⟩
  subst S
  obtain ⟨jt, hjt, htparams⟩ := hterm
  have hforced : ∀ I, IsMaximumIndependentOn G (H ∪ T) I → v ∈ I :=
    fun I hI => hatt.host_root_mem_every_maximum_of_terminal_nonpos hG hsmaller htparams hjt hbad hI
  obtain ⟨root, hfan⟩ := exists_component_rootedFan G hG (H ∪ T)
    (mem_union_left T hatt.host_root_mem) hconn
  let ι := (G.induce (((H ∪ T).erase v : Finset V) : Set V)).ConnectedComponent
  let B := deletedCenterBranch G (H ∪ T) v
  let it : ι := hatt.blockComponent
  have hBt : B it = T := (hatt.block_eq_deletedCenterBranch hconn).symm
  have hrt : root it = c := hatt.component_fan_root_eq hconn root hfan
  have hitparams : InducedIso.BranchParameters G (B it) (root it) jt := by
    rwa [hBt, hrt]
  have hfinish (up : Finset ι) (hup : up.card ≤ 1) (hit : it ∉ up)
      (hadj : ∀ i ∈ (univ : Finset ι) \ up, ∀ x ∈ B i,
        3 ≤ degreeOn G (H ∪ T) x → G.Adj v x) :
      0 < adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) := by
    have hparams : ∀ i ∈ (univ : Finset ι) \ up,
        ∃ j : Fin 8, InducedIso.BranchParameters G (B i) (root i) j := by
      intro i hi
      exact hfan.eight_branch_types_of_forced_center hG hsmaller hbad hforced (mem_univ _)
        (deletedCenterBranch_connected G (H ∪ T) v i) (hadj i hi)
    have hchoices : ∀ i : ι, ∃ j : Fin 8,
        (i ∈ (univ : Finset ι) \ up → InducedIso.BranchParameters G (B i) (root i) j) ∧
        (i = it → j = jt) := by
      intro i
      by_cases hi : i = it
      · subst i
        exact ⟨jt, fun _ => hitparams, fun _ => rfl⟩
      · by_cases hd : i ∈ (univ : Finset ι) \ up
        · obtain ⟨j, hj⟩ := hparams i hd
          exact ⟨j, fun _ => hj, fun he => (hi he).elim⟩
        · exact ⟨0, fun he => (hd he).elim, fun he => (hi he).elim⟩
    choose kind hk hkt using hchoices
    apply hfan.adjustedMean_pos_of_split_eight_types hG hsmaller up (subset_univ _) hup hvdeg
      kind hk _ hforced
    refine ⟨it, mem_sdiff.mpr ⟨mem_univ _, hit⟩, ?_⟩
    rw [hkt it rfl]
    rcases hjt with rfl | rfl <;> decide
  by_cases hrv : r = v
  · subst r
    apply hfinish ∅ (by simp) (by simp)
    intro i _ x hx hxd
    have hxS := mem_of_mem_erase (deletedCenterBranch_subset G (H ∪ T) v i hx)
    have hxv := (mem_erase.mp (deletedCenterBranch_subset G (H ∪ T) v i hx)).1
    have hle := hbound x hxS hxd
    rw [dist_self] at hle
    let f : G.induce ((H ∪ T : Finset V) : Set V) →g G := ⟨Subtype.val, fun h => h⟩
    have hpos := ((hconn.preconnected ⟨v, mem_union_left T hatt.host_root_mem⟩
      ⟨x, hxS⟩).map f).pos_dist_of_ne hxv.symm
    change 0 < G.dist v x at hpos
    exact dist_eq_one_iff_adj.mp (by omega)
  · have hr : r ∈ (H ∪ T).erase v := mem_erase.mpr ⟨hrv, mem_union_left T hrH⟩
    let ip : ι := (G.induce (((H ∪ T).erase v : Finset V) : Set V)).connectedComponentMk ⟨r, hr⟩
    apply hfinish {ip} (by simp)
    · simpa [it, ip] using hatt.blockComponent_ne_hostComponent hconn hrH hrv
    · intro i hi x hx hxd
      have hin : i ≠ ip := by simpa only [mem_sdiff, mem_univ, true_and, mem_singleton] using hi
      exact branching_adj_of_depth_bound G hG (H ∪ T) hconn hr hbound i hin hx hxd

#print axioms IsPenultimateSeed.adjustedMean_pos
end ForestUnimodality
