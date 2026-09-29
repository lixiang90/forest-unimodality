import ForestUnimodality.ShortLegReal
import ForestUnimodality.TerminalBlockRecurrence

/-! Unordered actual leg lists are covered by the finite short-leg
classification. The conclusion explicitly separates the 45 remaining
families from a strictly positive residual on the whole real interval. -/
namespace ForestUnimodality.ShortLegData
open MeanTerminalClosure TerminalBlockRecurrence

theorem residualReal_perm {legs other : List ℕ} (hp : legs.Perm other)
    (odd : Bool) (delta : ℕ) (r : ℝ) :
    residualReal odd legs delta r = residualReal odd other delta r := by
  unfold residualReal
  rw [(hp.map ratio).prod_eq, (hp.map excess).sum_eq, (hp.map deletedExcess).sum_eq]

theorem exists_canonical_short_legs (odd : Bool) (legs : List ℕ)
    (hpos : ∀ l ∈ legs, 0 < l) (hshort : ∀ l ∈ legs, l ≤ 13)
    (hpar : ∀ l ∈ legs, l % 2 = if odd then 1 else 0) :
    ∃ fan, fan.length = legs.length ∧ DescendingBounded (legBound odd) fan ∧
      (legsOf odd fan).Perm legs := by
  let index := fun l => if odd then l / 2 else (l - 2) / 2
  let raw := legs.map index
  let fan := raw.mergeSort (fun i j => decide (j ≤ i))
  have hp : fan.Perm raw := List.mergeSort_perm _ _
  have hbound : ∀ i ∈ raw, i < legBound odd := by
    intro i hi
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hi
    have h1 := hpos l hl
    have h2 := hshort l hl
    have h3 := hpar l hl
    cases odd <;> dsimp [legBound, index] at h3 ⊢ <;> omega
  have heq : legsOf odd raw = legs := by
    unfold legsOf raw
    rw [List.map_map]
    calc
      _ = legs.map (fun l => l) := by
        apply List.map_congr_left
        intro l hl
        have h1 := hpos l hl
        have h2 := hpar l hl
        cases odd <;> dsimp [legLength, index] at h2 ⊢ <;> omega
      _ = legs := by simp
  refine ⟨fan, ?_, ?_, ?_⟩
  · simpa [raw] using hp.length_eq
  · exact descending_of_pairwise _ _ (fun i hi => hbound i (hp.mem_iff.mp hi))
      (List.pairwise_mergeSort' _ raw)
  · rw [← heq]
    exact hp.map (legLength odd)

theorem exceptional_mem_terminalLegs (odd : Bool) (fan : List ℕ) (delta : ℕ)
    (hdesc : DescendingBounded (legBound odd) fan)
    (he : exceptional odd (legsOf odd fan) delta = true) :
    legsOf odd fan ∈ terminalLegs := by
  cases odd with
  | false =>
    have hh : delta = 1 ∧ legsOf false fan = [2, 2] := by simpa [exceptional] using he
    simp [terminalLegs, hh.2]
  | true =>
    have hh : delta = 0 ∧ ((legsOf true fan).length = 2 ∨ legsOf true fan ∈ oddTriples) := by
      simpa [exceptional] using he
    rcases hh.2 with hlen | hm
    · apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨fan, ?_, rfl⟩
      exact (mem_enumerateFans _ _ _).mpr ⟨by simpa [legsOf] using hlen, hdesc⟩
    · exact List.mem_append_right _ hm

/-- All two- and three-leg lists of one parity, without any ordering
assumption, either belong to the 45 families up to permutation or have a
positive residual for the specified actual binary host state and ratio. -/
theorem short_legs_classification (odd : Bool) (legs : List ℕ) (delta : ℕ)
    (hm : legs.length = 2 ∨ legs.length = 3)
    (hpos : ∀ l ∈ legs, 0 < l) (hshort : ∀ l ∈ legs, l ≤ 13)
    (hpar : ∀ l ∈ legs, l % 2 = if odd then 1 else 0) (hd : delta ≤ 1)
    (r : ℝ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    (∃ canonical ∈ terminalLegs, legs.Perm canonical) ∨
      0 < residualReal odd legs delta r := by
  obtain ⟨fan, hlen, hdesc, hp⟩ := exists_canonical_short_legs odd legs hpos hshort hpar
  by_cases he : exceptional odd (legsOf odd fan) delta = true
  · exact Or.inl ⟨_, exceptional_mem_terminalLegs odd fan delta hdesc he, hp.symm⟩
  · apply Or.inr
    rw [← residualReal_perm hp odd delta r]
    exact finite_leg_real_positive odd fan delta (by rwa [hlen]) hdesc hd
      (Bool.eq_false_iff.mpr he) r hr1 hr3

#print axioms exists_canonical_short_legs
#print axioms exceptional_mem_terminalLegs
#print axioms short_legs_classification
end ForestUnimodality.ShortLegData
