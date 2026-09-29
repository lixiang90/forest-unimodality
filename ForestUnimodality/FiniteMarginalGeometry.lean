import ForestUnimodality.FiniteMarginalSupport

/-! A cheap necessary support condition, obtained directly from the same
complement matching argument. It avoids evaluating large integer counts
when deciding which (M,j) states require a kernel check. -/
namespace ForestUnimodality.FiniteMarginalSupport
open Finset

def geometrySupportCheck (pairs : List (ℕ × ℕ)) (m : ℕ) (j : ℤ) : Bool :=
  pairs.any fun nk => decide (j ≤ (nk.2 : ℤ) ∧
    2 * ((nk.2 : ℤ) - j).toNat ≤ nk.1 ∧
    m + ((nk.2 : ℤ) - j).toNat ≤ nk.1)

def geometryShifts (cap : ℕ) (pairs : List (ℕ × ℕ)) (m : ℕ) : List ℤ :=
  ((List.range (2 * cap + 1)).map (fun i : ℕ => (i : ℤ) - cap)).filter
    (geometrySupportCheck pairs m)

theorem geometrySupportCheck_bounds {cap m : ℕ} {pairs : List (ℕ × ℕ)} {j : ℤ}
    (hpairs : ∀ nk ∈ pairs, nk.1 ≤ cap ∧ nk.2 ≤ cap)
    (hs : geometrySupportCheck pairs m j = true) : -(cap : ℤ) ≤ j ∧ j ≤ cap := by
  obtain ⟨nk, hnk, hc⟩ := List.any_eq_true.mp hs
  have h := of_decide_eq_true hc
  have hb := hpairs nk hnk
  omega

theorem mem_geometryShifts {cap m : ℕ} {pairs : List (ℕ × ℕ)} {j : ℤ}
    (hpairs : ∀ nk ∈ pairs, nk.1 ≤ cap ∧ nk.2 ≤ cap)
    (hs : geometrySupportCheck pairs m j = true) : j ∈ geometryShifts cap pairs m := by
  obtain ⟨hjlo, hjhi⟩ := geometrySupportCheck_bounds hpairs hs
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨(j + cap).toNat, ?_, ?_⟩, hs⟩
  · apply List.mem_range.mpr
    omega
  · omega

variable {V : Type*} [DecidableEq V]

theorem actual_geometry_support {G : SimpleGraph V} (hG : G.IsAcyclic)
    {S B : Finset V} {z : ℝ} (hB : IsMaximumMarginalIndependentOn G S B z)
    (hz : 0 < z) (k : ℕ) (pairs : List (ℕ × ℕ)) (hpairs : (S.card, k) ∈ pairs)
    {y m : ℕ} (hw : 0 < hardCoreLayerWeight G S B z y m) :
    geometrySupportCheck pairs m ((k : ℤ) - y) = true := by
  classical
  have hcount := layerCount_pos_of_weight_pos hw
  obtain ⟨J, hJ⟩ := card_pos.mp hcount
  obtain ⟨hJI, hJy, hJm⟩ := mem_filter.mp hJ
  have hhalf := MarginalComplementMatching.independent_complement_card_le_half hG hB hz hJI
  have hmB : m ≤ B.card := by
    rw [← hJm]
    exact card_le_card (available_subset G B J)
  have hyC : y ≤ (S \ B).card := by
    rw [← hJy]
    exact card_le_card (mem_independentSubsets.mp hJI).1
  have hn := card_sdiff_add_card_eq_card hB.subset
  have hy : ((k : ℤ) - ((k : ℤ) - y)).toNat = y := by omega
  apply List.any_eq_true.mpr
  refine ⟨(S.card, k), hpairs, ?_⟩
  apply decide_eq_true
  simp only [hy]
  exact ⟨by omega, by omega, by omega⟩

#print axioms actual_geometry_support
#print axioms mem_geometryShifts
end ForestUnimodality.FiniteMarginalSupport
