import ForestUnimodality.SpiderStructure
import ForestUnimodality.ShortLegData
import ForestUnimodality.ShortLegClosure

/-! Actual short-leg spiders with at least four branches are strictly
positive. Every parameter bound is obtained from the proved path recurrence
and the finite rational path bounds; branch count remains unbounded. -/
namespace ForestUnimodality
open Finset
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_parameters {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    partitionFunction G (B i) (2 : ℝ) / partitionFunction G ((B i).erase (root i)) (2 : ℝ) =
        (ShortLegData.ratio (length i) : ℝ) ∧
      adjustedMeanPotential G (B i) (independenceNumberOn G (B i)) =
        (ShortLegData.excess (length i) : ℝ) ∧
      deletedRootExcess G (B i) (root i) = (ShortLegData.deletedExcess (length i) : ℝ) := by
  have ht := (h.branch_statistics hi).trans (ShortLegData.pathData_cast (length i)).symm
  have hZ := congrArg Prod.fst ht
  have hM := congrArg (fun p => p.2.1) ht
  have hA := congrArg (fun p => p.2.2.1) ht
  have hN := congrArg (fun p => p.2.2.2) ht
  have halpha := congrArg Prod.fst (h.branch_alpha_pair hi)
  dsimp [ShortLegData.castState] at hZ hM hA hN halpha
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ, hA]
    simp [ShortLegData.ratio]
  · unfold adjustedMeanPotential hardCoreMean ShortLegData.excess
    rw [hZ, hM, halpha, h.branch_card hi]
    push_cast
    ring
  · unfold deletedRootExcess hardCoreMean ShortLegData.deletedExcess
    rw [hA, hN, halpha, h.branch_card hi]
    push_cast
    ring

omit [DecidableEq ι] in
theorem IsSpiderOn.short_even_bounds {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s)
    (hshort : length i ≤ 13) (heven : length i % 2 = 0) :
    (5 / 3 : ℝ) ≤ partitionFunction G (B i) (2 : ℝ) /
        partitionFunction G ((B i).erase (root i)) (2 : ℝ) ∧
      (13 / 30 : ℝ) ≤ adjustedMeanPotential G (B i) (independenceNumberOn G (B i)) ∧
      -(11 / 60 : ℝ) ≤ deletedRootExcess G (B i) (root i) := by
  have hp := h.length_pos i hi
  have heq : 2 * ((length i - 2) / 2) + 2 = length i := by omega
  have hb := ShortLegData.even_bounds ((length i - 2) / 2) (by omega)
  rw [heq] at hb
  rw [(h.branch_parameters hi).1, (h.branch_parameters hi).2.1, (h.branch_parameters hi).2.2]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.1
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.2.1
  · simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.2.2

omit [DecidableEq ι] in
theorem IsSpiderOn.short_odd_bounds {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s)
    (hshort : length i ≤ 13) (hodd : length i % 2 = 1) :
    (2 : ℝ) ≤ partitionFunction G (B i) (2 : ℝ) /
        partitionFunction G ((B i).erase (root i)) (2 : ℝ) ∧
      (343 / 1140 : ℝ) ≤ adjustedMeanPotential G (B i) (independenceNumberOn G (B i)) ∧
      -(89 / 60 : ℝ) ≤ deletedRootExcess G (B i) (root i) := by
  have heq : 2 * (length i / 2) + 1 = length i := by omega
  have hb := ShortLegData.odd_bounds (length i / 2) (by omega)
  rw [heq] at hb
  rw [(h.branch_parameters hi).1, (h.branch_parameters hi).2.1, (h.branch_parameters hi).2.2]
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hb.1
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.2.1
  · simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb.2.2

theorem IsSpiderOn.adjustedMean_pos_of_four_even_short_legs
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hm : 4 ≤ s.card)
    (hshort : ∀ i ∈ s, length i ≤ 13) (heven : ∀ i ∈ s, length i % 2 = 0) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  let R := fun i => partitionFunction G (B i) (2 : ℝ) /
    partitionFunction G ((B i).erase (root i)) (2 : ℝ)
  let a := fun i => adjustedMeanPotential G (B i) (independenceNumberOn G (B i))
  let b := fun i => deletedRootExcess G (B i) (root i)
  let A := ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ)
  have hAp : 0 < A := prod_pos (fun i _ => partitionFunction_pos G _ (by norm_num : (0 : ℝ) ≤ 2))
  have hRP : (∏ i ∈ s, R i) * A = ∏ i ∈ s, partitionFunction G (B i) (2 : ℝ) := by
    dsimp [R, A]
    rw [prod_div_distrib, div_mul_cancel₀ _ (ne_of_gt hAp)]
  have hbds := fun i hi => h.short_even_bounds hi (hshort i hi) (heven i hi)
  have hres := ShortLegClosure.even_cluster_positive s R a b 3 (89 / 60) hm
    (fun i hi => (hbds i hi).1) (fun i hi => (hbds i hi).2.1)
    (fun i hi => (hbds i hi).2.2) (by norm_num) (by norm_num) (le_refl _)
  have hstate : ∀ i ∈ s, independenceNumberOn G (B i) =
      independenceNumberOn G ((B i).erase (root i)) := by
    intro i hi
    have hp := h.branch_alpha_pair hi
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    have he := heven i hi
    dsimp at h1 h2
    omega
  have hdef : (independenceNumberOn G S : ℝ) -
      (∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) = 1 := by
    rw [h.toIsRootedFanOn.alpha_of_root_state_zero hstate]
    push_cast
    ring
  have hid := h.toIsRootedFanOn.adjustedMean_identity
  rw [hdef, ← hRP] at hid
  have hpos : 0 < A * ((∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 89 / 60) +
      2 * (∑ i ∈ s, b i) + 89 / 60 + 31 / 20) := by
    apply mul_pos hAp
    nlinarith [hres]
  have heq : A * ((∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 89 / 60) +
      2 * (∑ i ∈ s, b i) + 89 / 60 + 31 / 20) =
      partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S (independenceNumberOn G S) := by
    rw [hid]
    dsimp [a, b, A]
    ring
  rw [heq] at hpos
  have hZ := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem IsSpiderOn.adjustedMean_pos_of_four_odd_short_legs
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hm : 4 ≤ s.card)
    (hshort : ∀ i ∈ s, length i ≤ 13) (hodd : ∀ i ∈ s, length i % 2 = 1) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  let R := fun i => partitionFunction G (B i) (2 : ℝ) /
    partitionFunction G ((B i).erase (root i)) (2 : ℝ)
  let a := fun i => adjustedMeanPotential G (B i) (independenceNumberOn G (B i))
  let b := fun i => deletedRootExcess G (B i) (root i)
  let A := ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ)
  have hAp : 0 < A := prod_pos (fun i _ => partitionFunction_pos G _ (by norm_num : (0 : ℝ) ≤ 2))
  have hRP : (∏ i ∈ s, R i) * A = ∏ i ∈ s, partitionFunction G (B i) (2 : ℝ) := by
    dsimp [R, A]
    rw [prod_div_distrib, div_mul_cancel₀ _ (ne_of_gt hAp)]
  have hbds := fun i hi => h.short_odd_bounds hi (hshort i hi) (hodd i hi)
  have hres := ShortLegClosure.odd_cluster_positive s R a b 3 hm
    (fun i hi => (hbds i hi).1) (fun i hi => (hbds i hi).2.1)
    (fun i hi => (hbds i hi).2.2) (by norm_num) (by norm_num)
  have hstate : ∀ i ∈ s, independenceNumberOn G (B i) =
      independenceNumberOn G ((B i).erase (root i)) + 1 := by
    intro i hi
    have hp := h.branch_alpha_pair hi
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    have ho := hodd i hi
    dsimp at h1 h2
    omega
  have hne : s.Nonempty := card_pos.mp (by omega)
  have hdef : (independenceNumberOn G S : ℝ) -
      (∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) = 0 := by
    rw [h.toIsRootedFanOn.alpha_of_root_state_one hne hstate]
    push_cast
    ring
  have hid := h.toIsRootedFanOn.adjustedMean_identity
  rw [hdef, ← hRP] at hid
  have hpos : 0 < A * ((∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 29 / 60) +
      2 * (∑ i ∈ s, b i) + 29 / 60 + 91 / 20) := by
    apply mul_pos hAp
    nlinarith [hres]
  have heq : A * ((∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 29 / 60) +
      2 * (∑ i ∈ s, b i) + 29 / 60 + 91 / 20) =
      partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S (independenceNumberOn G S) := by
    rw [hid]
    dsimp [a, b, A]
    ring
  rw [heq] at hpos
  have hZ := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

theorem IsSpiderOn.card_le_three_of_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    s.card ≤ 3 := by
  by_contra hn
  have hm : 4 ≤ s.card := by omega
  have hshort := fun i hi => h.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
    hI hbad hsmaller (i := i) hi
  have hpar := h.same_parity_of_minimal_adjustedMean_nonpos hI hbad hsmaller
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < s.card by omega)
  have hmod := Nat.mod_lt (length i) (by decide : 0 < 2)
  have hpos : 0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
    by_cases he : length i % 2 = 0
    · apply h.adjustedMean_pos_of_four_even_short_legs hm hshort
      intro j hj
      exact (hpar j hj i hi).trans he
    · have ho : length i % 2 = 1 := by omega
      apply h.adjustedMean_pos_of_four_odd_short_legs hm hshort
      intro j hj
      exact (hpar j hj i hi).trans ho
  rw [← hI.card_eq_independenceNumberOn] at hpos
  exact (not_lt_of_ge hbad) hpos

#print axioms IsSpiderOn.branch_parameters
#print axioms IsSpiderOn.adjustedMean_pos_of_four_even_short_legs
#print axioms IsSpiderOn.adjustedMean_pos_of_four_odd_short_legs
#print axioms IsSpiderOn.card_le_three_of_minimal_adjustedMean_nonpos
end ForestUnimodality
