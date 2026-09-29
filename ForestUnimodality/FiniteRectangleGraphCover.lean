import ForestUnimodality.FiniteRectangleCover
import ForestUnimodality.FiniteSourceWindow

namespace ForestUnimodality.FiniteRectangleCover
open FiniteSourceWindow

def Strip.sourceCheck {ι : Type*} (s : Strip ι) (w : Window) (N : ℕ) : Bool :=
  decide (s.qlo = w.qa ∧ s.qhi = w.qb ∧
    s.mlo ≤ w.rho * N / (2 * w.qb) ∧ s.mhi = (Stage350SourceTable.row w.parent).start)

variable {V ι : Type*} [DecidableEq V]

theorem Strip.actual_mean_lower (s : Strip ι) (w : Window) (N : ℕ)
    (hw : w.Valid) (hc : s.sourceCheck w N = true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hn : N ≤ S.card)
    (hq : z / (1 + z) ∈ Set.Icc (s.qlo : ℝ) (s.qhi : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z) :
    (s.mlo : ℝ) ≤ hardCoreAvailableMean G S B z := by
  have hp : s.qlo = w.qa ∧ s.qhi = w.qb ∧
      s.mlo ≤ w.rho * N / (2 * w.qb) ∧ s.mhi = (Stage350SourceTable.row w.parent).start :=
    of_decide_eq_true hc
  rw [hp.1, hp.2.1] at hq
  have hl : (s.mlo : ℝ) ≤ (w.rho : ℝ) * N / (2 * (w.qb : ℝ)) := by
    exact_mod_cast hp.2.2.1
  exact hl.trans (w.mean_lower hw hB hG hz hq hrank N hn)

theorem Strip.parent_domain (s : Strip ι) (w : Window) (N : ℕ)
    (hw : w.Valid) (hc : s.sourceCheck w N = true) {z m : ℝ}
    (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (s.qlo : ℝ) (s.qhi : ℝ))
    (hm : (s.mhi : ℝ) ≤ m) :
    z ∈ Set.Icc ((Stage350SourceTable.row w.parent).a : ℝ)
      ((Stage350SourceTable.row w.parent).b : ℝ) ∧
      ((Stage350SourceTable.row w.parent).start : ℝ) ≤ m := by
  have hp : s.qlo = w.qa ∧ s.qhi = w.qb ∧
      s.mlo ≤ w.rho * N / (2 * w.qb) ∧ s.mhi = (Stage350SourceTable.row w.parent).start :=
    of_decide_eq_true hc
  rw [hp.1, hp.2.1] at hq
  have ha := w.activity_bounds hw hz hq
  have hl : ((Stage350SourceTable.row w.parent).a : ℝ) ≤ (w.lower : ℝ) := by
    exact_mod_cast hw.parent_lower
  have hu : (w.upper : ℝ) ≤ ((Stage350SourceTable.row w.parent).b : ℝ) := by
    exact_mod_cast hw.parent_upper
  exact ⟨⟨hl.trans ha.1, ha.2.trans hu⟩, hp.2.2.2 ▸ hm⟩

/-- Every actual forest parameter belongs either to one finite rectangle or
to the large-mean region of a verified parent row. No probability or mean
interval is supplied as an extra graph hypothesis. -/
theorem actual_rectangle_or_parent {σ : Type*} (rectangles : ι → Rectangle)
    (strips : σ → Strip ι) (windows : σ → Window) (indices : List σ)
    (a b : ℚ) (N : ℕ)
    (hqcover : chainCheck (fun s => ((strips s).qlo, (strips s).qhi)) indices a b = true)
    (hstrips : ∀ s ∈ indices, (strips s).check rectangles = true)
    (hwindows : ∀ s ∈ indices, (windows s).Valid)
    (hsource : ∀ s ∈ indices, (strips s).sourceCheck (windows s) N = true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hn : N ≤ S.card)
    (hq : z / (1 + z) ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z) :
    (∃ i, (rectangles i).Contains (z / (1 + z)) (hardCoreAvailableMean G S B z)) ∨
    (∃ p : Fin 43, z ∈ Set.Icc ((Stage350SourceTable.row p).a : ℝ)
      ((Stage350SourceTable.row p).b : ℝ) ∧
      ((Stage350SourceTable.row p).start : ℝ) ≤ hardCoreAvailableMean G S B z) := by
  obtain ⟨s, hs, hqs⟩ := chainCheck_sound _ indices hqcover hq
  have hlo := (strips s).actual_mean_lower (windows s) N (hwindows s hs)
    (hsource s hs) hB hG hz hn hqs hrank
  by_cases hhi : hardCoreAvailableMean G S B z ≤ ((strips s).mhi : ℝ)
  · obtain ⟨i, _, hi⟩ := (strips s).check_sound rectangles (hstrips s hs) hqs ⟨hlo, hhi⟩
    exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨(windows s).parent, (strips s).parent_domain (windows s) N
      (hwindows s hs) (hsource s hs) hz hqs (le_of_not_ge hhi)⟩

#print axioms Strip.actual_mean_lower
#print axioms Strip.parent_domain
#print axioms actual_rectangle_or_parent

end ForestUnimodality.FiniteRectangleCover
