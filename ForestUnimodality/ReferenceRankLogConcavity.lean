import ForestUnimodality.MatchingUpperBound
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Coefficients of products of positive rank-one factors. Integer indexing
gives exact zero extension on the left, so no predecessor truncation occurs.
The stronger cross-ratio inequality is preserved by adjoining each factor. -/

namespace ForestUnimodality

noncomputable def referenceRank : List ℝ → ℤ → ℝ
  | [], k => if k = 0 then 1 else 0
  | d :: ds, k => referenceRank ds k + d * referenceRank ds (k - 1)

noncomputable def referencePolynomial (ds : List ℝ) : Polynomial ℝ :=
  (ds.map (fun d => 1 + Polynomial.C d * Polynomial.X)).prod

def RankCrossRatio (q : ℤ → ℝ) : Prop :=
  ∀ i j : ℤ, i ≤ j → q (i - 1) * q (j + 1) ≤ q i * q j

theorem RankCrossRatio.two_gap {q : ℤ → ℝ} (hq : RankCrossRatio q)
    (i j : ℤ) (hij : i ≤ j) : q (i - 2) * q (j + 1) ≤ q i * q (j - 1) := by
  by_cases heq : i = j
  · subst j
    have h := hq (i - 1) i (by omega)
    have he : i - 1 - 1 = i - 2 := by omega
    rw [he] at h
    simpa only [mul_comm] using h
  · have h1 := hq i (j - 1) (by omega)
    have h2 := hq (i - 1) j (by omega)
    have he1 : j - 1 + 1 = j := by omega
    have he2 : i - 1 - 1 = i - 2 := by omega
    rw [he1] at h1
    rw [he2] at h2
    exact h2.trans h1

theorem RankCrossRatio.adjoin_factor {q : ℤ → ℝ} (hq : RankCrossRatio q)
    {d : ℝ} (hd : 0 ≤ d) : RankCrossRatio (fun k => q k + d * q (k - 1)) := by
  intro i j hij
  have h0 := hq i j hij
  have h1 := hq (i - 1) (j - 1) (by omega)
  have h2 := hq.two_gap i j hij
  have hi2 : i - 1 - 1 = i - 2 := by omega
  have hj0 : j - 1 + 1 = j := by omega
  have hj1 : j + 1 - 1 = j := by omega
  rw [hi2, hj0] at h1
  have h1' := mul_le_mul_of_nonneg_left h1 (sq_nonneg d)
  have h2' := mul_le_mul_of_nonneg_left h2 hd
  dsimp only
  rw [hi2, hj1]
  nlinarith

theorem referenceRank_nonneg (ds : List ℝ) (hds : ∀ d ∈ ds, 0 ≤ d) (k : ℤ) :
    0 ≤ referenceRank ds k := by
  induction ds generalizing k with
  | nil => simp only [referenceRank]; split_ifs <;> norm_num
  | cons d ds ih =>
    have hd := hds d (by simp)
    have ht : ∀ e ∈ ds, 0 ≤ e := fun e he => hds e (by simp [he])
    exact add_nonneg (ih ht k) (mul_nonneg hd (ih ht (k - 1)))

theorem referenceRank_cross_ratio (ds : List ℝ) (hds : ∀ d ∈ ds, 0 ≤ d) :
    RankCrossRatio (referenceRank ds) := by
  induction ds with
  | nil =>
    intro i j hij
    have hnot : ¬ (i - 1 = 0 ∧ j + 1 = 0) := by omega
    simp only [referenceRank]
    split_ifs <;> norm_num at * <;> omega
  | cons d ds ih =>
    exact (ih (fun e he => hds e (by simp [he]))).adjoin_factor (hds d (by simp))

theorem referenceRank_log_concave (ds : List ℝ) (hds : ∀ d ∈ ds, 0 ≤ d) (k : ℤ) :
    referenceRank ds (k - 1) * referenceRank ds (k + 1) ≤ referenceRank ds k ^ 2 := by
  simpa only [pow_two] using referenceRank_cross_ratio ds hds k k (le_refl k)

theorem referenceRank_eq_zero_of_neg (ds : List ℝ) {k : ℤ} (hk : k < 0) :
    referenceRank ds k = 0 := by
  induction ds generalizing k with
  | nil => simp [referenceRank, ne_of_lt hk]
  | cons d ds ih => simp [referenceRank, ih hk, ih (show k - 1 < 0 by omega)]

theorem referenceRank_eq_zero_of_gt_length (ds : List ℝ) {k : ℤ}
    (hk : (ds.length : ℤ) < k) : referenceRank ds k = 0 := by
  induction ds generalizing k with
  | nil => simp only [List.length_nil, Nat.cast_zero] at hk; simp [referenceRank, ne_of_gt hk]
  | cons d ds ih =>
    have hk' : (ds.length : ℤ) + 1 < k := by simpa using hk
    simp [referenceRank, ih (show (ds.length : ℤ) < k by omega),
      ih (show (ds.length : ℤ) < k - 1 by omega)]

theorem referenceRank_pos_of_mem_support (ds : List ℝ) (hds : ∀ d ∈ ds, 0 < d)
    {k : ℤ} (hk0 : 0 ≤ k) (hkl : k ≤ ds.length) : 0 < referenceRank ds k := by
  induction ds generalizing k with
  | nil =>
    have hk : k = 0 := by simp only [List.length_nil, Nat.cast_zero] at hkl; omega
    simp [referenceRank, hk]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have ht : ∀ e ∈ ds, 0 < e := fun e he => hds e (by simp [he])
    have hn : ∀ e ∈ ds, 0 ≤ e := fun e he => (ht e he).le
    change 0 < referenceRank ds k + d * referenceRank ds (k - 1)
    by_cases hk : k ≤ ds.length
    · exact add_pos_of_pos_of_nonneg (ih ht hk0 hk)
        (mul_nonneg hd.le (referenceRank_nonneg ds hn _))
    · have hkl' : k ≤ (ds.length : ℤ) + 1 := by simpa using hkl
      exact add_pos_of_nonneg_of_pos (referenceRank_nonneg ds hn _)
        (mul_pos hd (ih ht (by omega) (by omega)))

theorem referenceRank_pos_iff (ds : List ℝ) (hds : ∀ d ∈ ds, 0 < d) (k : ℤ) :
    0 < referenceRank ds k ↔ 0 ≤ k ∧ k ≤ ds.length := by
  constructor
  · intro h
    constructor
    · by_contra hn
      rw [referenceRank_eq_zero_of_neg ds (by omega)] at h
      exact (lt_irrefl 0) h
    · by_contra hn
      rw [referenceRank_eq_zero_of_gt_length ds (by omega)] at h
      exact (lt_irrefl 0) h
  · rintro ⟨hk0, hkl⟩
    exact referenceRank_pos_of_mem_support ds hds hk0 hkl

/-- The sequence is the coefficient sequence of the actual factor product. -/
theorem referenceRank_nat_eq_coeff (ds : List ℝ) (k : ℕ) :
    referenceRank ds (k : ℤ) = (referencePolynomial ds).coeff k := by
  induction ds generalizing k with
  | nil => simp [referenceRank, referencePolynomial, Polynomial.coeff_one]
  | cons d ds ih =>
    have hp : referencePolynomial (d :: ds) =
        referencePolynomial ds * (1 + Polynomial.C d * Polynomial.X) := by
      simp only [referencePolynomial, List.map_cons, List.prod_cons]
      exact mul_comm _ _
    rw [referenceRank, hp, mul_add, mul_one, Polynomial.coeff_add, ← mul_assoc]
    cases k with
    | zero =>
      simp only [Nat.cast_zero]
      rw [Polynomial.coeff_mul_X_zero,
        referenceRank_eq_zero_of_neg ds (k := (0 : ℤ) - 1) (by norm_num)]
      simpa using ih 0
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      simp only [hk, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
      rw [ih (k + 1), ih k]
      ring

noncomputable def matchingReferenceWeights (a v : ℕ) : List ℝ :=
  List.replicate v 2 ++ List.replicate (a - v) 1

theorem matchingReferenceWeights_pos (a v : ℕ) :
    ∀ d ∈ matchingReferenceWeights a v, 0 < d := by
  intro d hd
  simp only [matchingReferenceWeights, List.mem_append, List.mem_replicate] at hd
  rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num

theorem matchingReferenceWeights_length (a v : ℕ) (hva : v ≤ a) :
    (matchingReferenceWeights a v).length = a := by
  simp only [matchingReferenceWeights, List.length_append, List.length_replicate]
  omega

theorem referencePolynomial_matchingReferenceWeights (a v : ℕ) :
    referencePolynomial (matchingReferenceWeights a v) =
      (1 + 2 * Polynomial.X) ^ v * (1 + Polynomial.X) ^ (a - v) := by
  simp [referencePolynomial, matchingReferenceWeights, List.map_append,
    List.prod_append, List.map_replicate, List.prod_replicate, Polynomial.C_ofNat]

theorem coeff_matching_polynomial_real (a v k : ℕ) :
    (((1 + 2 * Polynomial.X) ^ v * (1 + Polynomial.X) ^ (a - v) :
      Polynomial ℝ).coeff k) = (matchingUpperCount a v k : ℝ) := by
  rw [matching_polynomial_eq_sum]
  simp only [Polynomial.finsetSum_coeff, mul_assoc, Polynomial.coeff_natCast_mul,
    coeff_shifted_binomial, matchingUpperCount, Nat.cast_sum, Nat.cast_mul]

theorem referenceRank_matching_eq (a v k : ℕ) :
    referenceRank (matchingReferenceWeights a v) (k : ℤ) = (matchingUpperCount a v k : ℝ) := by
  rw [referenceRank_nat_eq_coeff, referencePolynomial_matchingReferenceWeights,
    coeff_matching_polynomial_real]

theorem matchingUpperCount_pos_iff (a v k : ℕ) (hva : v ≤ a) :
    0 < matchingUpperCount a v k ↔ k ≤ a := by
  have h := referenceRank_pos_iff (matchingReferenceWeights a v)
    (matchingReferenceWeights_pos a v) (k : ℤ)
  rw [referenceRank_matching_eq, matchingReferenceWeights_length a v hva] at h
  have h' : 0 < matchingUpperCount a v k ↔ 0 ≤ k ∧ k ≤ a := by exact_mod_cast h
  simpa only [Nat.zero_le, true_and] using h'

theorem matchingUpperCount_log_concave (a v k : ℕ) :
    matchingUpperCount a v k * matchingUpperCount a v (k + 2) ≤
      matchingUpperCount a v (k + 1) ^ 2 := by
  have h := referenceRank_log_concave (matchingReferenceWeights a v)
    (fun d hd => (matchingReferenceWeights_pos a v d hd).le) ((k + 1 : ℕ) : ℤ)
  have h0 : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
  have h2 : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
  rw [h0, h2, referenceRank_matching_eq, referenceRank_matching_eq,
    referenceRank_matching_eq] at h
  exact_mod_cast h

#print axioms referenceRank_cross_ratio
#print axioms referenceRank_pos_iff
#print axioms referenceRank_nat_eq_coeff
#print axioms matchingUpperCount_pos_iff
#print axioms matchingUpperCount_log_concave

end ForestUnimodality
