import ForestUnimodality.MessageWeightedResponse

/-! Exact logarithmic Cauchy weights for the message-dependent source
refinement. The number of children is unrestricted. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def sourceExactH (p : ℝ) : ℝ :=
  if p = 0 then 1 else p / (-Real.log (1 - p))

theorem sourceExactH_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    0 < sourceExactH p := by
  by_cases hzero : p = 0
  · simp [sourceExactH, hzero]
  · rw [sourceExactH, if_neg hzero]
    have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hzero)
    exact div_pos hpos
      (neg_pos.mpr (Real.log_neg (by linarith) (by linarith)))

theorem sourceExactH_ratio (p : ℝ) :
    p / sourceExactH p = -Real.log (1 - p) := by
  by_cases hzero : p = 0
  · simp [hzero, sourceExactH]
  · rw [sourceExactH, if_neg hzero]
    field_simp [hzero]

theorem sourceExactH_le_relaxed {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    sourceExactH p ≤ 1 - p / 2 := by
  by_cases hzero : p = 0
  · simp [sourceExactH, hzero]
  · have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hzero)
    have hlog : 0 < -Real.log (1 - p) :=
      neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
    rw [sourceExactH, if_neg hzero]
    apply (div_le_iff₀ hlog).mpr
    have hbound := (div_le_iff₀ (show 0 < 1 - p / 2 by linarith)).mp
      (source_probability_log_bound hp hp1)
    nlinarith

omit [DecidableEq V] in
theorem source_exact_response_cauchy (s : Finset V) (p d : V → ℝ)
    (hp : ∀ y ∈ s, 0 ≤ p y ∧ p y < 1) :
    (∑ y ∈ s, p y * d y) ^ 2 ≤
      (∑ y ∈ s, -Real.log (1 - p y)) *
        (∑ y ∈ s, p y * sourceExactH (p y) * d y ^ 2) := by
  have hH : ∀ y ∈ s, 0 < sourceExactH (p y) :=
    fun y hy => sourceExactH_pos (hp y hy).1 (hp y hy).2
  have hc := FiniteTilt.weighted_cauchy s (fun y => p y / sourceExactH (p y))
    (fun _ => 1) (fun y => sourceExactH (p y) * d y)
    (fun y hy => div_nonneg (hp y hy).1 (hH y hy).le)
  have hcross : FiniteTilt.numerator s (fun y => p y / sourceExactH (p y))
      (fun y => 1 * (sourceExactH (p y) * d y)) = ∑ y ∈ s, p y * d y := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    field_simp [(hH y hy).ne']
  have hone : FiniteTilt.numerator s (fun y => p y / sourceExactH (p y))
      (fun _ => (1 : ℝ) ^ 2) = ∑ y ∈ s, -Real.log (1 - p y) := by
    simp only [FiniteTilt.numerator, one_pow, mul_one]
    exact sum_congr rfl (fun y _ => sourceExactH_ratio (p y))
  have hsq : FiniteTilt.numerator s (fun y => p y / sourceExactH (p y))
      (fun y => (sourceExactH (p y) * d y) ^ 2) =
        ∑ y ∈ s, p y * sourceExactH (p y) * d y ^ 2 := by
    apply sum_congr rfl
    intro y hy
    dsimp only
    field_simp [(hH y hy).ne']
  rwa [hcross, hone, hsq] at hc

omit [DecidableEq V] in
theorem source_exact_positive_response_capacity (s : Finset V) (p d : V → ℝ) (T : ℝ)
    (hp : ∀ y ∈ s, 0 ≤ p y ∧ p y < 1)
    (hcapacity : (∑ y ∈ s, -Real.log (1 - p y)) ≤ T) :
    (max 0 (∑ y ∈ s, p y * d y)) ^ 2 / T ≤
      ∑ y ∈ s, p y * sourceExactH (p y) * (max 0 (d y)) ^ 2 := by
  have hE : 0 ≤ ∑ y ∈ s, p y * sourceExactH (p y) * (max 0 (d y)) ^ 2 :=
    sum_nonneg (fun y hy => mul_nonneg
      (mul_nonneg (hp y hy).1 (sourceExactH_pos (hp y hy).1 (hp y hy).2).le) (sq_nonneg _))
  have hT : 0 ≤ T := (sum_nonneg (fun y hy =>
    neg_nonneg.mpr (Real.log_nonpos (by linarith [(hp y hy).2])
      (by linarith [(hp y hy).1])))).trans hcapacity
  by_cases hzero : T = 0
  · rw [hzero, div_zero]
    exact hE
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  apply (div_le_iff₀ hTpos).mpr
  have hsnonneg : 0 ≤ ∑ y ∈ s, p y * max 0 (d y) :=
    sum_nonneg (fun y hy => mul_nonneg (hp y hy).1 (le_max_left _ _))
  have hmax : max 0 (∑ y ∈ s, p y * d y) ≤ ∑ y ∈ s, p y * max 0 (d y) := by
    apply max_le hsnonneg
    exact sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (le_max_right _ _) (hp y hy).1)
  have hsquare := pow_le_pow_left₀ (le_max_left 0 (∑ y ∈ s, p y * d y)) hmax 2
  have hc := source_exact_response_cauchy s p (fun y => max 0 (d y)) hp
  have he := mul_le_mul_of_nonneg_right hcapacity hE
  nlinarith

theorem SourceMessages.exact_positive_response_capacity
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (max 0 (a x - d x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * sourceExactH (p y) * (max 0 (d y)) ^ 2 := by
  have he : a x - d x = ∑ y ∈ sourceChildren S parent x, p y * d y := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    linarith
  rw [he]
  exact source_exact_positive_response_capacity _ p d _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_log_sum_le_capacity hactivity hx)

theorem SourceMessages.exact_negative_response_capacity
    {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) {x : V} (hx : x ∈ S) :
    (max 0 (d x - a x)) ^ 2 / sourceLogCapacity b (p x) ≤
      ∑ y ∈ sourceChildren S parent x, p y * sourceExactH (p y) * (max 0 (-d y)) ^ 2 := by
  have he : d x - a x = ∑ y ∈ sourceChildren S parent x, p y * (-d y) := by
    have hr := h.response x hx
    unfold sourceChildResponse at hr
    simp only [mul_neg, sum_neg_distrib]
    linarith
  rw [he]
  exact source_exact_positive_response_capacity _ p (fun y => -d y) _
    (fun y hy => h.probability y (mem_filter.mp hy).1) (h.child_log_sum_le_capacity hactivity hx)

#print axioms sourceExactH_pos
#print axioms sourceExactH_ratio
#print axioms sourceExactH_le_relaxed
#print axioms source_exact_response_cauchy
#print axioms SourceMessages.exact_positive_response_capacity
#print axioms SourceMessages.exact_negative_response_capacity

end ForestUnimodality
