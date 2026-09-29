import ForestUnimodality.TerminalBlockAttachment

/-! Actual center-rooted spiders and genuine pendant bridge extensions have
the terminal statistics used by the checked closure. No branch-count or
length bound is needed for this exact state-identification theorem. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u v
variable {V : Type u} {ι : Type v} [DecidableEq V] [DecidableEq ι]

noncomputable def spiderCenterState (s : Finset ι) (length : ι → ℕ) : BlockState ℝ :=
  let A := ∏ i ∈ s, (pathBranchStatistics (length i)).1
  let B := 2 * ∏ i ∈ s, (pathBranchStatistics (length i)).2.2.1
  let a0 : ℕ := ∑ i ∈ s, (length i + 1) / 2
  let a1 : ℕ := 1 + ∑ i ∈ s, length i / 2
  let alpha := max a0 a1
  ⟨A, B, A * (∑ i ∈ s, (pathBranchStatistics (length i)).2.1 /
      (pathBranchStatistics (length i)).1),
    B * (1 + ∑ i ∈ s, (pathBranchStatistics (length i)).2.2.2 /
      (pathBranchStatistics (length i)).2.2.1),
    ((1 + ∑ i ∈ s, length i : ℕ) : ℝ), alpha, ((alpha - a0 : ℕ) : ℝ)⟩

omit [DecidableEq ι] in
theorem terminalState_cast_toList (s : Finset ι) (length : ι → ℕ) :
    castState (terminalState (s.toList.map length)) = spiderCenterState s length := by
  unfold terminalState castState spiderCenterState
  simp only [← ShortLegData.pathData_cast, ShortLegData.castState]
  push_cast
  simp only [List.map_map, Function.comp_def, Finset.prod_map_toList,
    Finset.sum_map_toList]
  push_cast
  rfl

theorem IsSpiderOn.actualBlockState_center {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) :
    actualBlockState G S c = spiderCenterState s length := by
  have hZ : ∀ i ∈ s, partitionFunction G (B i) (2 : ℝ) =
      (pathBranchStatistics (length i)).1 := fun i hi => congrArg Prod.fst (h.branch_statistics hi)
  have hM : ∀ i ∈ s, hardCoreMomentNumerator G (B i) 1 (2 : ℝ) =
      (pathBranchStatistics (length i)).2.1 :=
    fun i hi => congrArg (fun p => p.2.1) (h.branch_statistics hi)
  have hA : ∀ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ) =
      (pathBranchStatistics (length i)).2.2.1 :=
    fun i hi => congrArg (fun p => p.2.2.1) (h.branch_statistics hi)
  have hN : ∀ i ∈ s, hardCoreMomentNumerator G ((B i).erase (root i)) 1 (2 : ℝ) =
      (pathBranchStatistics (length i)).2.2.2 :=
    fun i hi => congrArg (fun p => p.2.2.2) (h.branch_statistics hi)
  have hP := prod_congr rfl hZ
  have hD := prod_congr rfl hA
  have hU : (∑ i ∈ s, hardCoreMean G (B i) 2) =
      ∑ i ∈ s, (pathBranchStatistics (length i)).2.1 / (pathBranchStatistics (length i)).1 := by
    apply sum_congr rfl
    intro i hi
    unfold hardCoreMean
    rw [hM i hi, hZ i hi]
  have hW : (∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 2) =
      ∑ i ∈ s, (pathBranchStatistics (length i)).2.2.2 /
        (pathBranchStatistics (length i)).2.2.1 := by
    apply sum_congr rfl
    intro i hi
    unfold hardCoreMean
    rw [hN i hi, hA i hi]
  have hAlpha : (∑ i ∈ s, independenceNumberOn G (B i)) =
      ∑ i ∈ s, (length i + 1) / 2 :=
    sum_congr rfl (fun i hi => congrArg Prod.fst (h.branch_alpha_pair hi))
  have hAlphaD : (∑ i ∈ s, independenceNumberOn G ((B i).erase (root i))) =
      ∑ i ∈ s, length i / 2 :=
    sum_congr rfl (fun i hi => congrArg Prod.snd (h.branch_alpha_pair hi))
  have hOrder : (∑ i ∈ s, (B i).card) = ∑ i ∈ s, length i :=
    sum_congr rfl (fun _ hi => h.branch_card hi)
  have hzdel : partitionFunction G (S.erase c) (2 : ℝ) =
      ∏ i ∈ s, (pathBranchStatistics (length i)).1 := by
    rw [h.erase_center, h.separated.partitionFunction_biUnion, hP]
  have hmdel : hardCoreMomentNumerator G (S.erase c) 1 (2 : ℝ) =
      (∑ i ∈ s, (pathBranchStatistics (length i)).2.1 /
        (pathBranchStatistics (length i)).1) *
        (∏ i ∈ s, (pathBranchStatistics (length i)).1) := by
    rw [hardCore_first_moment_eq_mean_mul_partition G _ (by norm_num : (0 : ℝ) ≤ 2),
      hzdel, h.erase_center, h.separated.mean_biUnion (by norm_num : (0 : ℝ) ≤ 2), hU]
  have hadel : independenceNumberOn G (S.erase c) = ∑ i ∈ s, (length i + 1) / 2 := by
    rw [h.erase_center, h.separated.independenceNumber_biUnion, hAlpha]
  unfold actualBlockState spiderCenterState rootDefect
  rw [hzdel, hmdel, hadel, h.toIsRootedFanOn.partitionFunction_eq G (2 : ℝ),
    h.toIsRootedFanOn.firstMoment (by norm_num : (0 : ℝ) ≤ 2),
    h.toIsRootedFanOn.independenceNumber, h.toIsRootedFanOn.card,
    hP, hD, hU, hW, hAlpha, hAlphaD, hOrder]
  simp only [Nat.add_comm _ 1]
  congr 1 <;> ring

/-- An arbitrary finite branch indexing is converted to its actual list of
leg lengths. The chosen ordering is immaterial to the statistics. -/
theorem IsSpiderOn.actualBlockState_terminalState {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) :
    actualBlockState G S c = castState (terminalState (s.toList.map length)) := by
  rw [terminalState_cast_toList, h.actualBlockState_center]

theorem IsSpiderOn.actualBlockState_bridgeState {G : SimpleGraph V} {S T : Finset V} {c w : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (b : ℕ)
    (hp : PendantPathExtension G S c (b - 1) T w) :
    actualBlockState G T w = castState (bridgeState (s.toList.map length) b) := by
  rw [hp.actualBlockState_eq, h.actualBlockState_terminalState,
    bridgeState, cast_iterate]

omit [DecidableEq V] [DecidableEq ι] in
theorem terminalState_perm {legs legs' : List ℕ} (hp : legs.Perm legs') :
    terminalState legs = terminalState legs' := by
  have hA := (hp.map (fun n => (ShortLegData.pathData n).1)).prod_eq
  have hB := (hp.map (fun n => (ShortLegData.pathData n).2.2.1)).prod_eq
  have hMA := (hp.map (fun n => (ShortLegData.pathData n).2.1 /
    (ShortLegData.pathData n).1)).sum_eq
  have hMB := (hp.map (fun n => (ShortLegData.pathData n).2.2.2 /
    (ShortLegData.pathData n).2.2.1)).sum_eq
  have ha0 := (hp.map (fun n => (n + 1) / 2)).sum_eq
  have ha1 := (hp.map (fun n => n / 2)).sum_eq
  unfold terminalState
  rw [hA, hB, hMA, hMB, ha0, ha1, hp.sum_eq]

theorem IsSpiderOn.actualBlockState_bridgeState_of_perm
    {G : SimpleGraph V} {S T : Finset V} {c w : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (b : ℕ)
    (hp : PendantPathExtension G S c (b - 1) T w) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) :
    actualBlockState G T w = castState (bridgeState legs b) := by
  rw [h.actualBlockState_bridgeState b hp, bridgeState, terminalState_perm hlegs]
  rfl

/-- Actual spider plus actual pendant bridge, with leg lengths accepted up
to permutation. No numerical state-equality premise remains. -/
theorem IsRootedBlockAttachment.adjustedMean_pos_of_spiderBridge
    {G : SimpleGraph V} {H S T : Finset V} {v c w : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsRootedBlockAttachment G H v T w) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    (hspider : IsSpiderOn G S c s B root tip length) (b : ℕ) (hb : 1 ≤ b)
    (hp : PendantPathExtension G S c (b - 1) T w) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hne : ¬ (b = 1 ∧ (legs = [3,3] ∨ legs = [5,3]))) :
    0 < adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) :=
  h.adjustedMean_pos_of_terminalState hG hsmaller legs hl b hb hne
    (hspider.actualBlockState_bridgeState_of_perm b hp legs hlegs)

#print axioms IsSpiderOn.actualBlockState_terminalState
#print axioms IsSpiderOn.actualBlockState_bridgeState
#print axioms IsRootedBlockAttachment.adjustedMean_pos_of_spiderBridge
end ForestUnimodality
