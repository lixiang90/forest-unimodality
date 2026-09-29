import ForestUnimodality.UnitActivityTreeBranches
import ForestUnimodality.UnitActivityBranchDensity
import ForestUnimodality.UnitActivitySmallForest

/-! The numerical branch inequalities applied to the actual unit-activity
distribution of a tree.  The only induction input concerns strictly smaller
vertex sets, with their original graph and actual hard-core means. -/
namespace ForestUnimodality
open Finset
namespace UnitActivityFanDensity
open UnitActivityBranchDensity
variable {V : Type*} [DecidableEq V]

def kind (n : ℕ) : Kind := if n = 1 then 0 else if n = 2 then 1 else if n = 3 then 2 else 3

theorem branch_estimate (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) (u : V) (hu : u ∈ B) (hBS : B ⊆ S) (hBl : B.card < S.card)
    (hconn : (G.induce (B : Set V)).Connected)
    (hsmall : ∀ T : Finset V, T ⊆ S → T.card < S.card → 0 < T.card → T.card ≠ 2 →
      276393 / 1000000 * (T.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G T 1) :
    (a : ℝ) * B.card + (fullExcess (kind B.card) : ℝ) ≤ hardCoreMean G B 1 ∧
    (a : ℝ) * B.card + (deletedExcess (kind B.card) : ℝ) ≤ hardCoreMean G (B.erase u) 1 ∧
    (ratioLower (kind B.card) : ℝ) ≤
      partitionFunction G (B.erase u) (1 : ℝ) / partitionFunction G B 1 ∧
    partitionFunction G (B.erase u) (1 : ℝ) / partitionFunction G B 1 ≤
      (ratioUpper (kind B.card) : ℝ) := by
  have hn : 0 < B.card := card_pos.mpr ⟨u, hu⟩
  by_cases h1 : B.card = 1
  · obtain ⟨hm, hd, hr⟩ := UnitActivitySmallForest.singleton_statistics G B h1 hu
    norm_num [kind, h1, fullExcess, deletedExcess, ratioLower, ratioUpper, a, c, hm, hd, hr]
  by_cases h2 : B.card = 2
  · obtain ⟨hm, hd, hr⟩ := UnitActivitySmallForest.edge_statistics G B h2 hconn hu
    norm_num [kind, h2, fullExcess, deletedExcess, ratioLower, ratioUpper, a, c, hm, hd, hr]
  by_cases h3 : B.card = 3
  · obtain ⟨hm, hd, hl, hr⟩ := UnitActivitySmallForest.three_statistics G B hG h3 hu
    norm_num [kind, h3, fullExcess, deletedExcess, ratioLower, ratioUpper, a, c]
    exact ⟨hm, hd, hl, hr⟩
  · have hn4 : 4 ≤ B.card := by omega
    have hdcard := card_erase_add_one hu
    have hDsub : B.erase u ⊆ S := (erase_subset _ _).trans hBS
    have hDlt : (B.erase u).card < S.card := by omega
    have hm := hsmall B hBS hBl hn h2
    have hd := hsmall (B.erase u) hDsub hDlt (by omega) (by omega)
    norm_num at hm hd
    obtain ⟨hl, hr⟩ := UnitActivitySmallForest.deleted_ratio_bounds G B hu
    have hdc : ((B.erase u).card : ℝ) + 1 = B.card := by exact_mod_cast hdcard
    norm_num [kind, h1, h2, h3, fullExcess, deletedExcess, ratioLower, ratioUpper, a, c]
    refine ⟨hm, ?_, hl, hr⟩
    linarith

#print axioms branch_estimate
end UnitActivityFanDensity

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem IsRootedFanOn.unitActivity_density_lower
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) (hs : 3 ≤ s.card)
    (hconn : ∀ i ∈ s, (G.induce (B i : Set V)).Connected) (hG : G.IsAcyclic)
    (hsmall : ∀ T : Finset V, T ⊆ S → T.card < S.card → 0 < T.card → T.card ≠ 2 →
      276393 / 1000000 * (T.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G T 1) :
    276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1 := by
  classical
  let K := fun i => UnitActivityFanDensity.kind (B i).card
  let R := fun i => partitionFunction G ((B i).erase (root i)) (1 : ℝ) /
    partitionFunction G (B i) 1
  let r : ℝ := 1 / (1 + ∏ i ∈ s, R i)
  have hdata : ∀ i ∈ s,
      (UnitActivityBranchDensity.a : ℝ) * (B i).card +
          (UnitActivityBranchDensity.fullExcess (K i) : ℝ) ≤ hardCoreMean G (B i) 1 ∧
      (UnitActivityBranchDensity.a : ℝ) * (B i).card +
          (UnitActivityBranchDensity.deletedExcess (K i) : ℝ) ≤
        hardCoreMean G ((B i).erase (root i)) 1 ∧
      (UnitActivityBranchDensity.ratioLower (K i) : ℝ) ≤ R i ∧
      R i ≤ (UnitActivityBranchDensity.ratioUpper (K i) : ℝ) := by
    intro i hi
    have hBS : B i ⊆ S := by
      intro x hx
      rw [h.vertices]
      exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)
    have hBl : (B i).card < S.card := by
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hBS, ?_⟩
      intro he
      exact h.center_not_mem i hi (he ▸ h.center_mem)
    exact UnitActivityFanDensity.branch_estimate G hG S (B i) (root i)
      (h.root_mem i hi) hBS hBl (hconn i hi) hsmall
  have hnum := UnitActivityBranchDensity.branching_lower s K R hs
    (fun i hi => (hdata i hi).2.2.1) (fun i hi => (hdata i hi).2.2.2)
  change (UnitActivityBranchDensity.c : ℝ) ≤ 1 - r - (UnitActivityBranchDensity.a : ℝ) +
    ∑ i ∈ s, (r * (UnitActivityBranchDensity.fullExcess (K i) : ℝ) +
      (1 - r) * (UnitActivityBranchDensity.deletedExcess (K i) : ℝ)) at hnum
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hnum
  have hR : ∀ i ∈ s, 0 ≤ R i := by
    intro i hi
    exact div_nonneg (partitionFunction_pos _ _ (by norm_num)).le
      (partitionFunction_pos _ _ (by norm_num)).le
  have hp := Finset.prod_nonneg hR
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hfull := Finset.sum_le_sum (fun i hi => (hdata i hi).1)
  have hdel := Finset.sum_le_sum (fun i hi => (hdata i hi).2.1)
  rw [sum_add_distrib, ← mul_sum] at hfull hdel
  have hm := h.unitActivity_mean_mixture
  change hardCoreMean G S 1 = r * (∑ i ∈ s, hardCoreMean G (B i) 1) +
    (1 - r) * (1 + ∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 1) at hm
  have hc : (S.card : ℝ) = (∑ i ∈ s, ((B i).card : ℝ)) + 1 := by
    exact_mod_cast h.card
  norm_num [UnitActivityBranchDensity.a, UnitActivityBranchDensity.c] at hnum hfull hdel
  rw [hc]
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hfull),
    mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hdel)]

#print axioms IsRootedFanOn.unitActivity_density_lower
end ForestUnimodality
