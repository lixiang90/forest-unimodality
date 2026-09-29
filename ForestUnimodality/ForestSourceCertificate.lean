import ForestUnimodality.ForestSourcePhi

/-! Sound assembly of a scalar independent-support source certificate.
All graph budgets are proved from the actual forest distribution. The full
continuous scalar nonnegativity condition remains an explicit input. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- Fixed vertex marks and actual occupation marginals have the same mean. -/
theorem heterogeneousMean_marked_eq_sum_marginals (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) :
    heterogeneousMean G S activity (markedSum a) =
      ∑ x ∈ S, heterogeneousMarginal G S activity x * a x := by
  classical
  have hnum : FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity) (markedSum a) =
      ∑ x ∈ S, a x * FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity)
        (fun J => if x ∈ J then 1 else 0) := by
    unfold FiniteTilt.numerator
    calc
      _ = ∑ J ∈ independentSubsets G S, ∑ x ∈ S,
          heterogeneousWeight activity J * (a x * (if x ∈ J then 1 else 0)) := by
        apply sum_congr rfl
        intro J hJ
        have hf : S.filter (fun x => x ∈ J) = J := by
          ext x
          simp only [mem_filter]
          exact ⟨And.right, fun hx => ⟨(mem_independentSubsets.mp hJ).1 hx, hx⟩⟩
        rw [← mul_sum]
        congr 1
        simp only [mul_ite, mul_one, mul_zero, ← sum_filter, hf]
        rfl
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
        apply sum_congr rfl
        intro J _
        ring
  unfold heterogeneousMean FiniteTilt.mean
  rw [hnum, sum_div]
  apply sum_congr rfl
  intro x _
  unfold heterogeneousMarginal heterogeneousMean FiniteTilt.mean
  ring

noncomputable def sourceIndicator (B : Finset V) (x : V) : ℝ := if x ∈ B then 1 else 0

theorem markedSum_sourceIndicator (B J : Finset V) :
    markedSum (sourceIndicator B) J = ((J ∩ B).card : ℝ) := by
  classical
  simp only [markedSum, sourceIndicator, ← sum_filter]
  have hf : J.filter (fun x => x ∈ B) = J ∩ B := by ext x; simp
  rw [hf]
  simp

def SourceMarkState (a parentA : ℝ) : Prop :=
  (a = 0 ∧ parentA = 0) ∨ (a = 0 ∧ parentA = 1) ∨ (a = 1 ∧ parentA = 0)

theorem SourceMessages.independent_mark_state {G : SimpleGraph V} {S B : Finset V}
    {activity : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity (sourceIndicator B) parent p d)
    (hB : G.IsIndepSet (B : Set V)) {x : V} (hx : x ∈ S) :
    SourceMarkState (sourceIndicator B x) (sourceParentMark (sourceIndicator B) (parent x)) := by
  classical
  cases he : parent x with
  | none =>
    by_cases hxB : x ∈ B <;> simp [SourceMarkState, sourceParentMark, sourceIndicator, hxB]
  | some y =>
    have hadj := (h.parent_mem x hx y he).2
    by_cases hxB : x ∈ B
    · have hyB : y ∉ B := fun hyB => hB hxB hyB hadj.ne hadj
      simp [SourceMarkState, sourceParentMark, sourceIndicator, hxB, hyB]
    · by_cases hyB : y ∈ B <;> simp [SourceMarkState, sourceParentMark, sourceIndicator, hxB, hyB]

/-- The source's eight multiplier roles, with signed response price allowed. -/
structure SourceRowParameters where
  A : ℝ
  C : ℝ
  logPrice : ℝ
  phiPrice : ℝ
  responsePrice : ℝ
  blockingPrice : ℝ
  positivePrice : ℝ → ℝ
  negativePrice : ℝ → ℝ

def SourceRowParameters.Admissible (P : SourceRowParameters) : Prop :=
  0 ≤ P.logPrice ∧ 0 ≤ P.phiPrice ∧ 0 ≤ P.blockingPrice ∧
    (∀ t, 0 ≤ P.positivePrice t) ∧ (∀ t, 0 ≤ P.negativePrice t)

noncomputable def sourceScalarRow (P : SourceRowParameters) (lower b a parentA p r z : ℝ) : ℝ :=
  r * (P.A + P.C * a) - r * (1 - p) * z ^ 2 -
    P.logPrice * (Real.log p - 2 * Real.log (1 - p) - Real.log lower) / p +
  P.positivePrice a * (1 / (p * sourceLogCapacity b p)) * (max 0 (a - z)) ^ 2 -
    P.positivePrice parentA * (1 - p / 2) * (max 0 z) ^ 2 +
  P.negativePrice a * (1 / (p * sourceLogCapacity b p)) * (max 0 (z - a)) ^ 2 -
    P.negativePrice parentA * (1 - p / 2) * (max 0 (-z)) ^ 2 +
  P.phiPrice * (r * (1 + sourcePhi lower b p) - 1) + P.responsePrice * (z - r * a) +
  P.blockingPrice * (r * ((a - z) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b p)) -
    (1 - r) * (1 - p) * z ^ 2)

/-- Full real-domain validity. At p=q only the true leaf response z=a is
required. No p/r/z sampling is substituted for this condition. -/
def SourceRowValid (P : SourceRowParameters) (lower b : ℝ) : Prop :=
  ∀ a parentA, SourceMarkState a parentA → ∀ p r z : ℝ,
    0 < p → p ≤ b / (1 + b) →
    1 / (1 + b * (1 - p)) ≤ r → r ≤ 1 →
    (p = b / (1 + b) → z = a) → 0 ≤ sourceScalarRow P lower b a parentA p r z


theorem source_scalar_row_mul (P : SourceRowParameters) (lower b a parentA p pi z : ℝ)
    (hp : p ≠ 0) :
    p * sourceScalarRow P lower b a parentA p (pi / p) z =
      P.A * pi + P.C * (pi * a) - pi * (1 - p) * z ^ 2 -
      P.logPrice * (Real.log p - 2 * Real.log (1 - p) - Real.log lower) +
      p * (P.positivePrice a * (1 / (p * sourceLogCapacity b p)) * (max 0 (a - z)) ^ 2 -
        P.positivePrice parentA * (1 - p / 2) * (max 0 z) ^ 2) +
      p * (P.negativePrice a * (1 / (p * sourceLogCapacity b p)) * (max 0 (z - a)) ^ 2 -
        P.negativePrice parentA * (1 - p / 2) * (max 0 (-z)) ^ 2) +
      P.phiPrice * (p * ((pi / p) * (1 + sourcePhi lower b p) - 1)) +
      P.responsePrice * (p * z - pi * a) +
      P.blockingPrice * (p * ((pi / p) * ((a - z) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b p)) -
        (1 - pi / p) * (1 - p) * z ^ 2)) := by
  unfold sourceScalarRow
  field_simp
  ring

/-- Complete coefficient accounting for the scalar row and every true budget. -/
theorem source_scalar_row_sum (G : SimpleGraph V) (S : Finset V) (activity a : V → ℝ)
    (parent : V → Option V) (p d : V → ℝ) (P : SourceRowParameters) (lower b : ℝ)
    (hp : ∀ x ∈ S, p x ≠ 0) :
    (∑ x ∈ S, p x * sourceScalarRow P lower b (a x) (sourceParentMark a (parent x)) (p x)
      (heterogeneousMarginal G S activity x / p x) (d x)) =
      P.A * (∑ x ∈ S, heterogeneousMarginal G S activity x) +
      P.C * (∑ x ∈ S, heterogeneousMarginal G S activity x * a x) -
      (∑ x ∈ S, heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2) -
      P.logPrice * (∑ x ∈ S, (Real.log (p x) - 2 * Real.log (1 - p x) - Real.log lower)) +
      sourcePositiveCapacityBudget S a parent p d b P.positivePrice +
      sourceNegativeCapacityBudget S a parent p d b P.negativePrice +
      P.phiPrice * sourcePhiBudget G S activity p lower b +
      P.responsePrice * ((∑ x ∈ S, p x * d x) - (∑ x ∈ S, heterogeneousMarginal G S activity x * a x)) +
      P.blockingPrice * sourceBlockingBudget G S activity a p d b := by
  calc
    _ = ∑ x ∈ S,
      (P.A * heterogeneousMarginal G S activity x + P.C * (heterogeneousMarginal G S activity x * a x) -
      heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2 -
      P.logPrice * (Real.log (p x) - 2 * Real.log (1 - p x) - Real.log lower) +
      p x * (P.positivePrice (a x) * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (a x - d x)) ^ 2 -
        P.positivePrice (sourceParentMark a (parent x)) * (1 - p x / 2) * (max 0 (d x)) ^ 2) +
      p x * (P.negativePrice (a x) * (1 / (p x * sourceLogCapacity b (p x))) * (max 0 (d x - a x)) ^ 2 -
        P.negativePrice (sourceParentMark a (parent x)) * (1 - p x / 2) * (max 0 (-d x)) ^ 2) +
      P.phiPrice * (p x * ((heterogeneousMarginal G S activity x / p x) * (1 + sourcePhi lower b (p x)) - 1)) +
      P.responsePrice * (p x * d x - heterogeneousMarginal G S activity x * a x) +
      P.blockingPrice * (p x * ((heterogeneousMarginal G S activity x / p x) *
        ((a x - d x) ^ 2 / sourceOddsCapacity b (sourceLogCapacity b (p x))) -
        (1 - heterogeneousMarginal G S activity x / p x) * (1 - p x) * d x ^ 2))) := by
      apply sum_congr rfl
      intro x hx
      exact source_scalar_row_mul P lower b (a x) (sourceParentMark a (parent x)) (p x)
        (heterogeneousMarginal G S activity x) (d x) (hp x hx)
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sourcePositiveCapacityBudget,
        sourceNegativeCapacityBudget, sourcePhiBudget, sourceBlockingBudget]


/-- Soundness of the complete continuous scalar source certificate for one
fixed independent set B. All message and global budget facts are discharged
by actual forest theorems; only scalar row validity remains external. -/
theorem forest_independent_source_variance_of_scalar_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B : Set V)) (activity : V → ℝ)
    {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b)
    (P : SourceRowParameters) (hP : P.Admissible) (hvalid : SourceRowValid P lower b) :
    heterogeneousVariance G S activity (markedSum (sourceIndicator B)) ≤
      P.A * (∑ x ∈ S, heterogeneousMarginal G S activity x) +
      P.C * (∑ x ∈ S, heterogeneousMarginal G S activity x * sourceIndicator B x) := by
  have hact : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b :=
    fun x hx => ⟨hlower.trans_le (hactivity x hx).1, (hactivity x hx).2⟩
  obtain ⟨parent, p, d, hm, hmean, hvar⟩ := exists_forest_source_messages_moments G hG S activity
    (sourceIndicator B) (fun x hx => (hact x hx).1.le)
  have hp : ∀ x ∈ S, 0 < p x := fun x hx => hm.probability_pos (fun y hy => (hact y hy).1) hx
  have hrow : 0 ≤ ∑ x ∈ S, p x * sourceScalarRow P lower b (sourceIndicator B x)
      (sourceParentMark (sourceIndicator B) (parent x)) (p x) (heterogeneousMarginal G S activity x / p x) (d x) := by
    apply sum_nonneg
    intro x hx
    apply mul_nonneg (hp x hx).le
    apply hvalid _ _ (hm.independent_mark_state hB hx) _ _ _ (hp x hx) (hm.probability_le_bound hact hx)
      (hm.retention_bounds hact hx).1 (hm.retention_bounds hact hx).2
    exact hm.response_at_probability_endpoint hact hx
  have hsum := source_scalar_row_sum G S activity (sourceIndicator B) parent p d P lower b
    (fun x hx => (hp x hx).ne')
  have hpos := hm.positive_capacity_budget_scaled hact P.positivePrice hP.2.2.2.1
  have hneg := hm.negative_capacity_budget_scaled hact P.negativePrice hP.2.2.2.2
  have hphi := hm.phi_budget_scaled hlower hactivity
  have hblock := hm.blocking_capacity_budget_scaled hact
  have hlog := hm.log_mass_nonneg hlower (fun x hx => (hactivity x hx).1)
  have hresponse : (∑ x ∈ S, p x * d x) -
      (∑ x ∈ S, heterogeneousMarginal G S activity x * sourceIndicator B x) = 0 := by
    rw [← hmean, heterogeneousMean_marked_eq_sum_marginals]
    exact sub_self _
  rw [hresponse, mul_zero, ← hvar] at hsum
  have hlogPrice := mul_nonneg hP.1 hlog
  have hphiPrice := mul_nonpos_of_nonneg_of_nonpos hP.2.1 hphi
  have hblockPrice := mul_nonpos_of_nonneg_of_nonpos hP.2.2.1 hblock
  linarith

/-- The same theorem stated with the actual random counts K=|J| and
K_B=|J intersect B|. B is fixed across all allowed heterogeneous activities. -/
theorem forest_independent_count_variance_of_scalar_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B : Set V)) (activity : V → ℝ)
    {lower b : ℝ} (hlower : 0 < lower)
    (hactivity : ∀ x ∈ S, lower ≤ activity x ∧ activity x ≤ b)
    (P : SourceRowParameters) (hP : P.Admissible) (hvalid : SourceRowValid P lower b) :
    heterogeneousVariance G S activity (fun J => ((J ∩ B).card : ℝ)) ≤
      P.A * heterogeneousMean G S activity (fun J => (J.card : ℝ)) +
      P.C * heterogeneousMean G S activity (fun J => ((J ∩ B).card : ℝ)) := by
  have hones : (fun J : Finset V => (J.card : ℝ)) = markedSum (fun _ : V => (1 : ℝ)) := by
    funext J
    simp [markedSum]
  have hmark : (fun J : Finset V => ((J ∩ B).card : ℝ)) = markedSum (sourceIndicator B) := by
    funext J
    exact (markedSum_sourceIndicator B J).symm
  rw [hones, hmark, heterogeneousMean_marked_eq_sum_marginals,
    heterogeneousMean_marked_eq_sum_marginals]
  simp only [mul_one]
  exact forest_independent_source_variance_of_scalar_certificate G hG S B hB activity hlower hactivity P hP hvalid

#print axioms heterogeneousMean_marked_eq_sum_marginals
#print axioms source_scalar_row_sum
#print axioms forest_independent_source_variance_of_scalar_certificate
#print axioms forest_independent_count_variance_of_scalar_certificate
end ForestUnimodality
