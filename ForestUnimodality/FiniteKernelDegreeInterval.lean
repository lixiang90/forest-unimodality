import ForestUnimodality.FiniteKernelDegreePropagation

/-! A single rational-friendly lower bound controls all later degrees and
every activity in a closed interval. -/
namespace ForestUnimodality.FiniteKernelInterpolation
open Finset

theorem transform_antitone_degree {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {N n : ℕ} (hn : N ≤ n) :
    transform n t q ≤ transform N t q := by
  have hb0 : 0 ≤ 1 - q + q * t :=
    add_nonneg (sub_nonneg.mpr hq.2) (mul_nonneg hq.1 ht0)
  have hb1 : 1 - q + q * t ≤ 1 := by nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr ht1)]
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    calc
      transform (n + 1) t q = transform n t q * (1 - q + q * t) := by
        simp only [transform, pow_succ]
      _ ≤ transform n t q := mul_le_of_le_one_right (pow_nonneg hb0 _) hb1
      _ ≤ transform N t q := ih

theorem transform_le_lower_activity_degree {t a q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (haq : a ≤ q) {N n : ℕ} (hn : N ≤ n) :
    transform n t q ≤ transform N t a := by
  apply (transform_antitone_degree ht0 ht1 hq hn).trans
  apply pow_le_pow_left₀ (add_nonneg (sub_nonneg.mpr hq.2) (mul_nonneg hq.1 ht0))
  nlinarith [mul_nonneg (sub_nonneg.mpr haq) (sub_nonneg.mpr ht1)]

noncomputable def Row.degreeFloor {ι : Type*} (r : Row ι) (N : ℕ) (a b : ℝ) : ℝ :=
  r.dM * (2 * (N : ℝ) + 1) - r.B - r.dδ / 4 -
    ∑ i ∈ r.terms, r.price i * b * (1 - r.retention i) * transform N (r.retention i) a

theorem Row.degreeFloor_le_increment {ι : Type*} (r : Row ι) (N n : ℕ)
    {a b q : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hq : q ∈ Set.Icc a b)
    (hdM : 0 ≤ r.dM) (hdδ : 0 ≤ r.dδ)
    (hp : ∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1)
    (hn : N ≤ n) : r.degreeFloor N a b ≤ r.degreeIncrement n q := by
  have hq01 : q ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.trans hq.1, hq.2.trans hb⟩
  have hb0 : 0 ≤ b := hq01.1.trans hq.2
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hM : r.dM * (2 * (N : ℝ) + 1) ≤ r.dM * (2 * (n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hdM
  have hv : q * (1 - q) ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hδ : r.dδ * q * (1 - q) ≤ r.dδ / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hv hdδ]
  have hs : (∑ i ∈ r.terms, r.price i * q * (1 - r.retention i) * transform n (r.retention i) q) ≤
      ∑ i ∈ r.terms, r.price i * b * (1 - r.retention i) * transform N (r.retention i) a := by
    apply sum_le_sum
    intro i hi
    obtain ⟨hprice, ht0, ht1⟩ := hp i hi
    have ht := transform_le_lower_activity_degree ht0 ht1 hq01 hq.1 hn
    have hpos : 0 ≤ transform n (r.retention i) q := by
      unfold transform
      apply pow_nonneg
      exact add_nonneg (sub_nonneg.mpr hq01.2) (mul_nonneg hq01.1 ht0)
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hq.2 ht hpos hb0)
      (mul_nonneg hprice (sub_nonneg.mpr ht1))
    nlinarith only [h]
  unfold Row.degreeFloor Row.degreeIncrement
  linarith

theorem Row.residual_nonneg_from_interval_degree {ι : Type*} (r : Row ι)
    (hf : ∀ j, r.fixedPrice j = 0) (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hdM : 0 ≤ r.dM) (hdδ : 0 ≤ r.dδ)
    (hp : ∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1)
    (hfloor : 0 ≤ r.degreeFloor N a b)
    (hbase : ∀ q ∈ Set.Icc a b, ∀ j : ℤ, 0 ≤ r.residual N j q) :
    ∀ n, N ≤ n → ∀ q ∈ Set.Icc a b, ∀ j : ℤ, 0 ≤ r.residual n j q := by
  intro n hn q hq
  apply r.residual_nonneg_from_degree hf ⟨ha.trans hq.1, hq.2.trans hb⟩ N (hbase q hq)
  · intro m hm
    exact hfloor.trans (r.degreeFloor_le_increment N m ha hb hq hdM hdδ hp hm)
  · exact hn

#print axioms transform_antitone_degree
#print axioms Row.degreeFloor_le_increment
#print axioms Row.residual_nonneg_from_interval_degree
end ForestUnimodality.FiniteKernelInterpolation
