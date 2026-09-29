import ForestUnimodality.TerminalSpiderState

/-! The two exceptional bridge-one spiders are actual terminal branches of
types T33 and T35. State equality here follows from the actual spider
decomposition; no graph-shape isomorphism is assumed. -/
namespace ForestUnimodality
open Finset TerminalBlockRecurrence
universe u v
variable {V : Type u} {ι : Type v} [DecidableEq V] [DecidableEq ι]

omit [DecidableEq ι] in
theorem branchParameters_of_actualBlockState_eq {G : SimpleGraph V} {S : Finset V} {w : V}
    (i : Fin 8) (hw : w ∈ S)
    (hs : actualBlockState G S w = actualBlockState (MeanTerminalGraphs.branchGraph i)
      univ (MeanTerminalGraphs.branchRoot i)) :
    InducedIso.BranchParameters G S w i := by
  have hA := congrArg BlockState.A hs
  have hB := congrArg BlockState.B hs
  have hMA := congrArg BlockState.MA hs
  have hMB := congrArg BlockState.MB hs
  have hN := congrArg BlockState.N hs
  have ha := congrArg BlockState.alpha hs
  have hd := congrArg BlockState.delta hs
  dsimp only [actualBlockState] at hA hB hMA hMB hN ha hd
  have hZ : partitionFunction G S (2 : ℝ) =
      partitionFunction (MeanTerminalGraphs.branchGraph i) univ 2 := by linarith
  have hM : hardCoreMomentNumerator G S 1 (2 : ℝ) =
      hardCoreMomentNumerator (MeanTerminalGraphs.branchGraph i) univ 1 2 := by linarith
  refine ⟨hw, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : S.card = (univ : Finset (Fin (MeanTerminalGraphs.branchOrder i))).card := by
      exact_mod_cast hN
    simpa using hc
  · rw [hZ, hA]
    exact MeanTerminalGraphs.actual_branch_ratio i
  · calc
      adjustedMeanPotential G S (independenceNumberOn G S) =
          adjustedMeanPotential (MeanTerminalGraphs.branchGraph i) univ
            (independenceNumberOn (MeanTerminalGraphs.branchGraph i) univ) := by
        unfold adjustedMeanPotential hardCoreMean
        rw [hM, hZ, ha, hN]
      _ = _ := MeanTerminalGraphs.actual_branch_excess i
  · unfold hardCoreMean
    rw [hMA, hA, ha, hN]
    exact MeanTerminalGraphs.actual_branch_deleted_excess i
  · have he : rootDefect (MeanTerminalGraphs.branchGraph i) univ
        (MeanTerminalGraphs.branchRoot i) = 0 := by
      simp [rootDefect, MeanTerminalGraphs.actual_branch_root_state_zero i]
    rw [he, Nat.cast_zero, rootDefect_cast] at hd
    have hc : independenceNumberOn G S = independenceNumberOn G (S.erase w) := by
      exact_mod_cast (show (independenceNumberOn G S : ℝ) =
        independenceNumberOn G (S.erase w) by linarith)
    exact hc

omit [DecidableEq V] [DecidableEq ι] in
theorem terminal_model_state (i : Fin 8) :
    actualBlockState (MeanTerminalGraphs.branchGraph i) univ (MeanTerminalGraphs.branchRoot i) =
      ⟨(MeanTerminalGraphs.expectedStatistics i).deletedPartition,
        (MeanTerminalGraphs.expectedStatistics i).partition -
          (MeanTerminalGraphs.expectedStatistics i).deletedPartition,
        (MeanTerminalGraphs.expectedStatistics i).deletedFirstMoment,
        (MeanTerminalGraphs.expectedStatistics i).firstMoment -
          (MeanTerminalGraphs.expectedStatistics i).deletedFirstMoment,
        MeanTerminalGraphs.branchOrder i,
        (MeanTerminalGraphs.expectedStatistics i).independence, 0⟩ := by
  simp only [actualBlockState, rootDefect,
    MeanTerminalGraphs.partition_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.deletedPartition_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.firstMoment_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.deletedFirstMoment_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.independence_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.deletedIndependence_eq_statistics (MeanTerminalGraphs.branchGraph i) univ
      (MeanTerminalGraphs.branchRoot i),
    MeanTerminalGraphs.actual_branch_statistics, card_univ, Fintype.card_fin]
  fin_cases i <;> norm_num [MeanTerminalGraphs.expectedStatistics]

omit [DecidableEq V] [DecidableEq ι] in
theorem terminalState_33_eq_model :
    castState (terminalState [3,3]) =
      actualBlockState (MeanTerminalGraphs.branchGraph 0) univ (MeanTerminalGraphs.branchRoot 0) := by
  rw [terminal_model_state]
  norm_num [terminalState, castState, ShortLegData.pathData, ShortLegData.transfer,
    MeanTerminalGraphs.expectedStatistics, MeanTerminalGraphs.branchOrder]

omit [DecidableEq V] [DecidableEq ι] in
theorem terminalState_53_eq_model :
    castState (terminalState [5,3]) =
      actualBlockState (MeanTerminalGraphs.branchGraph 1) univ (MeanTerminalGraphs.branchRoot 1) := by
  rw [terminal_model_state]
  norm_num [terminalState, castState, ShortLegData.pathData, ShortLegData.transfer,
    MeanTerminalGraphs.expectedStatistics, MeanTerminalGraphs.branchOrder]

theorem IsSpiderOn.exceptional_branchParameters_33 {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length)
    (hl : (s.toList.map length).Perm [3,3]) :
    InducedIso.BranchParameters G S c 0 := by
  apply branchParameters_of_actualBlockState_eq 0 h.center_mem
  rw [h.actualBlockState_terminalState, terminalState_perm hl, terminalState_33_eq_model]

theorem IsSpiderOn.exceptional_branchParameters_53 {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length)
    (hl : (s.toList.map length).Perm [5,3]) :
    InducedIso.BranchParameters G S c 1 := by
  apply branchParameters_of_actualBlockState_eq 1 h.center_mem
  rw [h.actualBlockState_terminalState, terminalState_perm hl, terminalState_53_eq_model]

/-- Once a genuine terminal spider and its bridge have been classified into
the 45 leg lists, nonpositive adjusted mean forces bridge length one and
one of the two actual exceptional branch parameter types. -/
theorem IsRootedBlockAttachment.terminal_type_of_nonpos
    {G : SimpleGraph V} {H S T : Finset V} {v c w : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsRootedBlockAttachment G H v T w) (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} (H ∪ T).card)
    (hspider : IsSpiderOn G S c s B root tip length) (b : ℕ) (hb : 1 ≤ b)
    (hp : PendantPathExtension G S c (b - 1) T w) (legs : List ℕ)
    (hlegs : (s.toList.map length).Perm legs) (hl : legs ∈ terminalLegs)
    (hbad : adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ≤ 0) :
    b = 1 ∧ ∃ i : Fin 8, (i = 0 ∨ i = 1) ∧ InducedIso.BranchParameters G T w i := by
  have he : b = 1 ∧ (legs = [3,3] ∨ legs = [5,3]) := by
    by_contra hn
    have hh := h.adjustedMean_pos_of_spiderBridge hG hsmaller hspider b hb hp
      legs hlegs hl hn
    exact (not_lt_of_ge hbad) hh
  refine ⟨he.1, ?_⟩
  rcases he with ⟨rfl, hlists⟩
  simp only [Nat.sub_self] at hp
  cases hp with
  | zero _ =>
    rcases hlists with rfl | rfl
    · exact ⟨0, Or.inl rfl, hspider.exceptional_branchParameters_33 hlegs⟩
    · exact ⟨1, Or.inr rfl, hspider.exceptional_branchParameters_53 hlegs⟩

#print axioms branchParameters_of_actualBlockState_eq
#print axioms IsSpiderOn.exceptional_branchParameters_33
#print axioms IsSpiderOn.exceptional_branchParameters_53
#print axioms IsRootedBlockAttachment.terminal_type_of_nonpos
end ForestUnimodality
