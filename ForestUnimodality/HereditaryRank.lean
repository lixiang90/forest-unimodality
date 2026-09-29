import ForestUnimodality.NormalizedRankStep
import ForestUnimodality.ReferenceRankLogConcavity
import ForestUnimodality.MatchingReferenceTail
import Mathlib.Data.Fintype.BigOperators

/-! Actual deletion-closed families in products of colored rank-one factors.
The adjacent-rank inequality is proved from the finite configuration counts,
not imposed on the family as a hypothesis. -/

namespace ForestUnimodality.HereditaryRank

open Finset
open Classical

/-- Each factor is absent, or carries exactly one of its colors. -/
def Config : List ℕ → Type
  | [] => Unit
  | d :: ds => Option (Fin d) × Config ds

instance configFintype : (ds : List ℕ) → Fintype (Config ds)
  | [] => inferInstanceAs (Fintype Unit)
  | d :: ds => by
    letI := configFintype ds
    exact inferInstanceAs (Fintype (Option (Fin d) × Config ds))

/-- Number of occupied coordinates, with integer indexing to avoid truncation. -/
def rank : {ds : List ℕ} → Config ds → ℤ
  | [], _ => 0
  | _ :: _, (o, x) => (if o.isSome then 1 else 0) + rank x

/-- A configuration can only lose occupied coordinates; colors cannot change. -/
def Below : {ds : List ℕ} → Config ds → Config ds → Prop
  | [], _, _ => True
  | _ :: _, (o, x), (p, y) => (o = none ∨ o = p) ∧ Below x y

def Hereditary {ds : List ℕ} (P : Config ds → Prop) : Prop :=
  ∀ x y, Below x y → P y → P x

theorem below_refl {ds : List ℕ} (x : Config ds) : Below x x := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨Or.inr rfl, ih x.2⟩

theorem rank_bounds {ds : List ℕ} (x : Config ds) :
    0 ≤ rank x ∧ rank x ≤ ds.length := by
  induction ds with
  | nil => simp [rank]
  | cons d ds ih =>
    rcases x with ⟨o, x⟩
    have h := ih x
    cases o <;> simp only [rank, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Option.isSome_some, List.length_cons, Nat.cast_add, Nat.cast_one] <;> omega

noncomputable def rankLayer {ds : List ℕ} (P : Config ds → Prop) (k : ℤ) :
    Finset (Config ds) := by
  classical
  exact univ.filter fun x => P x ∧ rank x = k

noncomputable def rankCount {ds : List ℕ} (P : Config ds → Prop) (k : ℤ) : ℝ :=
  (rankLayer P k).card

@[simp] theorem mem_rankLayer {ds : List ℕ} (P : Config ds → Prop) (k : ℤ)
    (x : Config ds) : x ∈ rankLayer P k ↔ P x ∧ rank x = k := by
  simp [rankLayer]

theorem rankCount_eq_sum {ds : List ℕ} (P : Config ds → Prop) (k : ℤ) :
    rankCount P k = ∑ x : Config ds, if P x ∧ rank x = k then (1 : ℝ) else 0 := by
  classical
  simp [rankCount, rankLayer, Finset.sum_boole]

theorem rankCount_nonneg {ds : List ℕ} (P : Config ds → Prop) (k : ℤ) :
    0 ≤ rankCount P k := by
  exact Nat.cast_nonneg _

theorem rankCount_mono {ds : List ℕ} {P Q : Config ds → Prop}
    (hPQ : ∀ x, P x → Q x) (k : ℤ) : rankCount P k ≤ rankCount Q k := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  simp only [rankLayer, mem_filter, mem_univ, true_and] at hx ⊢
  exact ⟨hPQ x hx.1, hx.2⟩

theorem rankCount_eq_zero_of_neg {ds : List ℕ} (P : Config ds → Prop)
    {k : ℤ} (hk : k < 0) : rankCount P k = 0 := by
  classical
  rw [rankCount_eq_sum]
  apply Finset.sum_eq_zero
  intro x _
  have h := (rank_bounds x).1
  simp only [ite_eq_right_iff]
  intro hx
  omega

theorem rankCount_eq_zero_of_gt_length {ds : List ℕ} (P : Config ds → Prop)
    {k : ℤ} (hk : (ds.length : ℤ) < k) : rankCount P k = 0 := by
  classical
  rw [rankCount_eq_sum]
  apply Finset.sum_eq_zero
  intro x _
  have h := (rank_bounds x).2
  simp only [ite_eq_right_iff]
  intro hx
  omega

def fiber {d : ℕ} {ds : List ℕ} (P : Config (d :: ds) → Prop)
    (o : Option (Fin d)) : Config ds → Prop := fun x => P (o, x)

theorem Hereditary.fiber_hereditary {d : ℕ} {ds : List ℕ} {P : Config (d :: ds) → Prop}
    (hP : Hereditary P) (o : Option (Fin d)) : Hereditary (fiber P o) := by
  intro x y hxy hy
  exact hP (o, x) (o, y) ⟨Or.inr rfl, hxy⟩ hy

theorem Hereditary.present_subset_absent {d : ℕ} {ds : List ℕ}
    {P : Config (d :: ds) → Prop} (hP : Hereditary P) (c : Fin d) (x : Config ds) :
    fiber P (some c) x → fiber P none x := by
  exact hP (none, x) (some c, x) ⟨Or.inl rfl, below_refl x⟩

/-- The exact partition into absent and colored-present configurations. -/
theorem rankCount_cons {d : ℕ} {ds : List ℕ} (P : Config (d :: ds) → Prop) (k : ℤ) :
    rankCount P k = rankCount (fiber P none) k +
      ∑ c : Fin d, rankCount (fiber P (some c)) (k - 1) := by
  classical
  simp only [rankCount_eq_sum]
  change (∑ x : Option (Fin d) × Config ds,
    if P x ∧ @rank (d :: ds) x = k then (1 : ℝ) else 0) = _
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  have hshift (x : Config ds) : 1 + rank x = k ↔ rank x = k - 1 := by omega
  simp only [rank, fiber, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ↓reduceIte, zero_add, hshift]
  rfl

/-- Every family count is bounded by the full layer of the reference product. -/
theorem rankCount_all (ds : List ℕ) (k : ℤ) :
    rankCount (fun _ : Config ds => True) k =
      referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k := by
  induction ds generalizing k with
  | nil => simp [rankCount_eq_sum, Config, rank, referenceRank, eq_comm]
  | cons d ds ih =>
    rw [rankCount_cons]
    change rankCount (fun _ : Config ds => True) k +
      (∑ _c : Fin d, rankCount (fun _ : Config ds => True) (k - 1)) = _
    simp [ih, referenceRank]

theorem rankCount_le_reference {ds : List ℕ} (P : Config ds → Prop) (k : ℤ) :
    rankCount P k ≤ referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k := by
  rw [← rankCount_all]
  exact rankCount_mono (fun _ _ => trivial) k

theorem weights_nonneg (ds : List ℕ) : ∀ d ∈ ds.map (fun d : ℕ => (d : ℝ)), 0 ≤ d := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨e, _, rfl⟩
  positivity

theorem weights_pos (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    ∀ d ∈ ds.map (fun d : ℕ => (d : ℝ)), 0 < d := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
  exact_mod_cast hds e he

/-- Normalized ranks of every actual deletion-closed family are nonincreasing.
All integer indices are covered, including zero layers outside the support. -/
theorem normalized_adjacent_rank (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d)
    (P : Config ds → Prop) (hP : Hereditary P) (k : ℤ) :
    rankCount P (k + 1) * referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k ≤
      rankCount P k * referenceRank (ds.map (fun d : ℕ => (d : ℝ))) (k + 1) := by
  induction ds generalizing k with
  | nil =>
    by_cases hk : k < 0
    · rw [referenceRank_eq_zero_of_neg _ hk, rankCount_eq_zero_of_neg P hk]
      simp
    · rw [rankCount_eq_zero_of_gt_length P (by simpa using (show (0 : ℤ) < k + 1 by omega))]
      simpa only [zero_mul] using mul_nonneg (rankCount_nonneg P k)
        (referenceRank_nonneg _ (weights_nonneg []) (k + 1))
  | cons d ds ih =>
    by_cases hk : k < 0
    · rw [referenceRank_eq_zero_of_neg _ hk, rankCount_eq_zero_of_neg P hk]
      simp
    by_cases hk' : (ds.length : ℤ) < k
    · have ht : (((d :: ds).length : ℕ) : ℤ) < k + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      rw [rankCount_eq_zero_of_gt_length P ht]
      simpa only [zero_mul] using mul_nonneg (rankCount_nonneg P k)
        (referenceRank_nonneg _ (weights_nonneg (d :: ds)) (k + 1))
    have ht : ∀ e ∈ ds, 0 < e := fun e he => hds e (by simp [he])
    have hq1 : 0 < referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k := by
      apply referenceRank_pos_of_mem_support _ (weights_pos ds ht) (by omega)
      simpa only [List.length_map] using (show k ≤ (ds.length : ℤ) by omega)
    have ha := ih ht (fiber P none) (hP.fiber_hereditary none) k
    have hb :
        (∑ c : Fin d, rankCount (fiber P (some c)) k) *
            referenceRank (ds.map (fun d : ℕ => (d : ℝ))) (k - 1) ≤
        (∑ c : Fin d, rankCount (fiber P (some c)) (k - 1)) *
            referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro c _
      simpa only [show k - 1 + 1 = k by omega] using
        ih ht (fiber P (some c)) (hP.fiber_hereditary (some c)) (k - 1)
    have hsub : (∑ c : Fin d, rankCount (fiber P (some c)) k) ≤
        (d : ℝ) * rankCount (fiber P none) k := by
      have hs := Finset.sum_le_sum (s := (univ : Finset (Fin d)))
        (fun c _ => rankCount_mono (hP.present_subset_absent c) k)
      simpa using hs
    have h := normalized_rank_extension_step
      (referenceRank_nonneg _ (weights_nonneg ds) (k - 1)) hq1
      (referenceRank_nonneg _ (weights_nonneg ds) (k + 1))
      (show (0 : ℝ) ≤ d by positivity)
      (referenceRank_log_concave _ (weights_nonneg ds) k) ha hb hsub
    rw [rankCount_cons, rankCount_cons]
    simpa only [List.map_cons, referenceRank, show k + 1 - 1 = k by omega] using h

/-- Division form on the positive support, useful for the matching reference. -/
theorem normalized_rank_ratio (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d)
    (P : Config ds → Prop) (hP : Hereditary P) (k : ℤ)
    (hk0 : 0 ≤ k) (hkl : k + 1 ≤ ds.length) :
    rankCount P (k + 1) / referenceRank (ds.map (fun d : ℕ => (d : ℝ))) (k + 1) ≤
      rankCount P k / referenceRank (ds.map (fun d : ℕ => (d : ℝ))) k := by
  have hp (j : ℤ) (hj0 : 0 ≤ j) (hjl : j ≤ ds.length) :
      0 < referenceRank (ds.map (fun d : ℕ => (d : ℝ))) j := by
    apply referenceRank_pos_of_mem_support _ (weights_pos ds hds) hj0
    simpa using hjl
  exact (div_le_div_iff₀ (hp _ (by omega) hkl) (hp _ hk0 (by omega))).mpr
    (normalized_adjacent_rank ds hds P hP k)

/-- The reference matching has v two-color blocks and a-v singleton blocks. -/
def matchingColors (a v : ℕ) : List ℕ := List.replicate v 2 ++ List.replicate (a - v) 1

theorem matchingColors_pos (a v : ℕ) : ∀ d ∈ matchingColors a v, 0 < d := by
  intro d hd
  simp only [matchingColors, List.mem_append, List.mem_replicate] at hd
  rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

theorem matchingColors_length (a v : ℕ) (hva : v ≤ a) :
    (matchingColors a v).length = a := by
  simp only [matchingColors, List.length_append, List.length_replicate]
  omega

theorem matchingColors_weights (a v : ℕ) :
    (matchingColors a v).map (fun d : ℕ => (d : ℝ)) = matchingReferenceWeights a v := by
  simp [matchingColors, matchingReferenceWeights]

theorem normalized_matching_rank (a v k : ℕ)
    (P : Config (matchingColors a v) → Prop) (hP : Hereditary P) :
    rankCount P ((k + 1 : ℕ) : ℤ) * (matchingUpperCount a v k : ℝ) ≤
      rankCount P (k : ℤ) * (matchingUpperCount a v (k + 1) : ℝ) := by
  have h := normalized_adjacent_rank (matchingColors a v) (matchingColors_pos a v) P hP k
  rw [matchingColors_weights] at h
  have hk : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hk, referenceRank_matching_eq, referenceRank_matching_eq] at h
  exact h

/-- A genuine hereditary subfamily inherits the matching reference's tail.
Encoding a graph as this family remains a separate combinatorial obligation. -/
theorem matching_family_tail (a v k : ℕ) (hva : v ≤ a)
    (hk : (3 * a + v) / 6 + 1 ≤ k)
    (P : Config (matchingColors a v) → Prop) (hP : Hereditary P) :
    rankCount P ((k + 1 : ℕ) : ℤ) ≤ rankCount P (k : ℤ) := by
  by_cases hka : k ≤ a
  · have hq : (0 : ℝ) < matchingUpperCount a v k := by
      exact_mod_cast (matchingUpperCount_pos_iff a v k hva).mpr hka
    have htail : (matchingUpperCount a v (k + 1) : ℝ) ≤ matchingUpperCount a v k := by
      exact_mod_cast matchingUpperCount_tail a v k hva hk
    have h := (normalized_matching_rank a v k P hP).trans
      (mul_le_mul_of_nonneg_left htail (rankCount_nonneg P k))
    exact le_of_mul_le_mul_right h hq
  · rw [rankCount_eq_zero_of_gt_length P (by
      rw [matchingColors_length a v hva]
      exact_mod_cast (show a < k + 1 by omega))]
    exact rankCount_nonneg P k

#print axioms rankCount_cons
#print axioms Hereditary.present_subset_absent
#print axioms rankCount_all
#print axioms normalized_adjacent_rank
#print axioms normalized_rank_ratio
#print axioms matching_family_tail

end ForestUnimodality.HereditaryRank
