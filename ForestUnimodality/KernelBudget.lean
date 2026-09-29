import ForestUnimodality.BinomialKernel
import ForestUnimodality.HardCoreMixtureMoments
import ForestUnimodality.AnalyticInterval

/-! Finite expectation weak duality for mixed-binomial kernel budgets.
Only states of positive weight need a pointwise certificate. Actual graph
layer weights and centered moments are connected below; source bounds remain
explicit inequalities on that same finite probability space. -/

namespace ForestUnimodality.KernelBudget

open Finset

noncomputable def expect {α : Type*} (s : Finset α) (w f : α → ℝ) : ℝ :=
  ∑ x ∈ s, w x * f x

theorem expect_const {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∑ x ∈ s, w x = 1) (c : ℝ) : expect s w (fun _ => c) = c := by
  rw [expect, ← sum_mul, hw, one_mul]

theorem expect_add {α : Type*} (s : Finset α) (w f g : α → ℝ) :
    expect s w (fun x => f x + g x) = expect s w f + expect s w g := by
  simp only [expect, mul_add, sum_add_distrib]

theorem expect_sub {α : Type*} (s : Finset α) (w f g : α → ℝ) :
    expect s w (fun x => f x - g x) = expect s w f - expect s w g := by
  simp only [expect, mul_sub, sum_sub_distrib]

theorem expect_const_mul {α : Type*} (s : Finset α) (w f : α → ℝ) (c : ℝ) :
    expect s w (fun x => c * f x) = c * expect s w f := by
  simp only [expect, mul_left_comm, mul_sum]

theorem expect_sum {α ι : Type*} (s : Finset α) (w : α → ℝ)
    (t : Finset ι) (f : ι → α → ℝ) :
    expect s w (fun x => ∑ i ∈ t, f i x) = ∑ i ∈ t, expect s w (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

/-- Zero-probability states impose no certificate obligation. -/
theorem expect_le_of_positive_support {α : Type*} (s : Finset α) (w f g : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x)
    (hfg : ∀ x ∈ s, 0 < w x → f x ≤ g x) : expect s w f ≤ expect s w g := by
  apply sum_le_sum
  intro x hx
  by_cases hzero : w x = 0
  · simp [hzero]
  · exact mul_le_mul_of_nonneg_left (hfg x hx (lt_of_le_of_ne (hw x hx) (Ne.symm hzero)))
      (hw x hx)

theorem second_moment_eq {α : Type*} (s : Finset α) (w M : α → ℝ)
    (hw : ∑ x ∈ s, w x = 1) {m : ℝ} (hm : expect s w M = m) :
    expect s w (fun x => M x ^ 2) =
      m ^ 2 + expect s w (fun x => (M x - m) ^ 2) := by
  have hp : (fun x => (M x - m) ^ 2) =
      (fun x => M x ^ 2 - (2 * m) * M x + m ^ 2) := by funext x; ring
  rw [hp, expect_add, expect_sub, expect_const_mul, expect_const s w hw, hm]
  ring

noncomputable def budget {ι η : Type*} (terms : Finset ι) (counts : Finset η)
    (A B dδ dM α β D : ℝ) (T rate : ι → ℝ) (U bound : η → ℝ) (m : ℝ) : ℝ :=
  A + B * m - dδ * (α * m + β) - dM * (m ^ 2 + D * m) -
    (∑ i ∈ terms, T i * Real.exp (-rate i * m)) - ∑ j ∈ counts, U j * bound j

theorem budget_eq_exponentialBudget {ι η : Type*} (terms : Finset ι) (counts : Finset η)
    (A B dδ dM α β D : ℝ) (T rate : ι → ℝ) (U bound : η → ℝ) (m : ℝ) :
    budget terms counts A B dδ dM α β D T rate U bound m =
      AnalyticInterval.exponentialBudget terms
        (A - dδ * β - ∑ j ∈ counts, U j * bound j)
        (B - dδ * α - dM * D) dM T rate m := by
  unfold budget AnalyticInterval.exponentialBudget
  ring

/-- The entire certificate row is averaged on one finite probability space.
The first moments are identities; the variance and transform bounds have the
directions needed by their nonnegative prices. -/
theorem budget_le_scaled_expect {α ι η : Type*}
    (s : Finset α) (w M δ f : α → ℝ) (terms : Finset ι) (counts : Finset η)
    (laplace : ι → α → ℝ) (countTest : η → α → ℝ)
    (scale A B C dδ dM α₀ β D m : ℝ) (T rate : ι → ℝ) (U bound : η → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1)
    (hm : expect s w M = m) (hδ : expect s w δ = 0)
    (hdδ : 0 ≤ dδ) (hdM : 0 ≤ dM)
    (hT : ∀ i ∈ terms, 0 ≤ T i) (hU : ∀ j ∈ counts, 0 ≤ U j)
    (hδsq : expect s w (fun x => δ x ^ 2) ≤ α₀ * m + β)
    (hvar : expect s w (fun x => (M x - m) ^ 2) ≤ D * m)
    (hlap : ∀ i ∈ terms, expect s w (laplace i) ≤ Real.exp (-rate i * m))
    (hcount : ∀ j ∈ counts, expect s w (countTest j) ≤ bound j)
    (hpoint : ∀ x ∈ s, 0 < w x →
      A + B * M x + C * δ x - dδ * δ x ^ 2 - dM * M x ^ 2 -
        (∑ i ∈ terms, T i * laplace i x) - ∑ j ∈ counts, U j * countTest j x ≤
          scale * f x) :
    budget terms counts A B dδ dM α₀ β D T rate U bound m ≤ scale * expect s w f := by
  have hraw := expect_le_of_positive_support s w _ _ hw hpoint
  simp only [expect_sub, expect_add, expect_const_mul, expect_sum,
    expect_const s w hsum, hm, hδ, mul_zero, add_zero] at hraw
  have hsecond : expect s w (fun x => M x ^ 2) ≤ m ^ 2 + D * m := by
    rw [second_moment_eq s w M hsum hm]
    linarith
  have hdδ' := mul_le_mul_of_nonneg_left hδsq hdδ
  have hdM' := mul_le_mul_of_nonneg_left hsecond hdM
  have hTl : (∑ i ∈ terms, T i * expect s w (laplace i)) ≤
      ∑ i ∈ terms, T i * Real.exp (-rate i * m) := by
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hlap i hi) (hT i hi)
  have hUl : (∑ j ∈ counts, U j * expect s w (countTest j)) ≤
      ∑ j ∈ counts, U j * bound j := by
    exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hcount j hj) (hU j hj)
  unfold budget
  linarith

theorem expect_pos_of_positive_budget {α ι η : Type*}
    (s : Finset α) (w f : α → ℝ) (terms : Finset ι) (counts : Finset η)
    (scale A B dδ dM α₀ β D m : ℝ) (T rate : ι → ℝ) (U bound : η → ℝ)
    (hscale : 0 < scale)
    (hbound : budget terms counts A B dδ dM α₀ β D T rate U bound m ≤
      scale * expect s w f)
    (hbudget : 0 < budget terms counts A B dδ dM α₀ β D T rate U bound m) :
    0 < expect s w f := by
  exact (mul_pos_iff_of_pos_left hscale).mp (hbudget.trans_le hbound)

theorem budget_pos_of_endpoints {ι η : Type*} (terms : Finset ι) (counts : Finset η)
    (A B dδ dM α β D : ℝ) (T rate : ι → ℝ) (U bound : η → ℝ)
    {lo hi m : ℝ} (hlohi : lo ≤ hi) (hdM : 0 ≤ dM)
    (hT : ∀ i ∈ terms, 0 ≤ T i)
    (hlo : 0 < budget terms counts A B dδ dM α β D T rate U bound lo)
    (hhi : 0 < budget terms counts A B dδ dM α β D T rate U bound hi)
    (hm : m ∈ Set.Icc lo hi) :
    0 < budget terms counts A B dδ dM α β D T rate U bound m := by
  simp only [budget_eq_exponentialBudget] at hlo hhi ⊢
  exact AnalyticInterval.positive_exponentialBudget_of_endpoints _ _ _ _ _ _
    hlohi hdM hT hlo hhi hm

#print axioms budget_le_scaled_expect
#print axioms expect_pos_of_positive_budget

end ForestUnimodality.KernelBudget

namespace ForestUnimodality

open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def hardCoreLayerExpectation (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
    hardCoreLayerWeight G S I z j m * f j m

theorem hardCoreLayerExpectation_eq_expect (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) (f : ℕ → ℕ → ℝ) :
    hardCoreLayerExpectation G S I z f =
      KernelBudget.expect (range ((S \ I).card + 1) ×ˢ range (I.card + 1))
        (fun p => hardCoreLayerWeight G S I z p.1 p.2) (fun p => f p.1 p.2) := by
  simp only [hardCoreLayerExpectation, KernelBudget.expect, sum_product]

theorem hardCoreLayerExpectation_centered_mean (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z)
    {k : ℝ} (hmean : hardCoreMean G S z = k) :
    hardCoreLayerExpectation G S I z (fun j m => k - binomialLayerMean j m z) = 0 := by
  have hp (j m : ℕ) :
      hardCoreLayerWeight G S I z j m * (k - binomialLayerMean j m z) =
        k * hardCoreLayerWeight G S I z j m -
          hardCoreLayerWeight G S I z j m * binomialLayerMean j m z := by ring
  simp only [hardCoreLayerExpectation, hp, sum_sub_distrib, ← mul_sum]
  rw [sum_hardCoreLayerWeight G S I hIS hI hz.le,
    ← hardCoreMean_eq_layer_mean G S I hIS hI hz, hmean]
  ring

theorem hardCoreLayerExpectation_centered_sq (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z)
    {k : ℝ} (hmean : hardCoreMean G S z = k) :
    hardCoreLayerExpectation G S I z (fun j m => (k - binomialLayerMean j m z) ^ 2) =
      hardCoreVariance G S z -
        (z / (1 + z)) * (1 - z / (1 + z)) * hardCoreAvailableMean G S I z := by
  rw [hardCoreVariance_eq_layer_variance G S I hIS hI hz]
  have heq : hardCoreLayerExpectation G S I z
      (fun j m => (k - binomialLayerMean j m z) ^ 2) =
      hardCoreLayerMeanVariance G S I z := by
    unfold hardCoreLayerExpectation hardCoreLayerMeanVariance
    rw [hmean]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro m _
    ring
  rw [heq]
  ring

noncomputable def hardCoreAvailableVariance (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) : ℝ := hardCoreLayerExpectation G S I z
      (fun _ m => ((m : ℝ) - hardCoreAvailableMean G S I z) ^ 2)

theorem hardCoreAvailableVariance_nonneg (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hardCoreAvailableVariance G S I z := by
  unfold hardCoreAvailableVariance hardCoreLayerExpectation
  exact sum_nonneg fun j _ => sum_nonneg fun m _ =>
    mul_nonneg (hardCoreLayerWeight_nonneg G S I hz j m) (sq_nonneg _)

noncomputable def hardCoreLayerLaplace (G : SimpleGraph V) (S I : Finset V)
    (z t : ℝ) : ℝ := hardCoreLayerExpectation G S I z
      (fun _ m => (1 - z / (1 + z) + z / (1 + z) * t) ^ m)

/-- The fixed shifted-index charge used by the finite stage-59 rows.
The shift is an integer and is never truncated to a natural number. -/
noncomputable def hardCoreFixedShiftMass (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) (k : ℕ) (r : ℤ) : ℝ := hardCoreLayerExpectation G S I z
      (fun j m => if (k : ℤ) - j = r then (1 - z / (1 + z)) ^ m else 0)

/-- Graph-specialized kernel weak duality. Mean centering and the conditional
variance subtraction come from the actual mixture identities. The remaining
variance, transform, and fixed-index estimates are explicit source bounds on
the same graph, independent set, and activity. -/
theorem averagedBinomialKernel_budget_lower {ι : Type*}
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z : ℝ} (hz : 0 < z) (k : ℕ) (hmean : hardCoreMean G S z = k)
    (terms : Finset ι) (counts : Finset ℤ)
    (wL wR wC scale A B C dδ dM α β D : ℝ)
    (T t rate : ι → ℝ) (U bound : ℤ → ℝ)
    (hdδ : 0 ≤ dδ) (hdM : 0 ≤ dM)
    (hT : ∀ i ∈ terms, 0 ≤ T i) (hU : ∀ r ∈ counts, 0 ≤ U r)
    (hvarK : hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + α) * hardCoreAvailableMean G S I z + β)
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * hardCoreAvailableMean G S I z)
    (hlap : ∀ i ∈ terms, hardCoreLayerLaplace G S I z (t i) ≤
      Real.exp (-rate i * hardCoreAvailableMean G S I z))
    (hcount : ∀ r ∈ counts, hardCoreFixedShiftMass G S I z k r ≤ bound r)
    (hpoint : ∀ j ∈ range ((S \ I).card + 1), ∀ m ∈ range (I.card + 1),
      0 < hardCoreLayerWeight G S I z j m →
      A + B * m + C * ((k : ℝ) - binomialLayerMean j m z) -
        dδ * ((k : ℝ) - binomialLayerMean j m z) ^ 2 - dM * (m : ℝ) ^ 2 -
        (∑ i ∈ terms, T i * (1 - z / (1 + z) + z / (1 + z) * t i) ^ m) -
        (∑ r ∈ counts, U r *
          (if (k : ℤ) - j = r then (1 - z / (1 + z)) ^ m else 0)) ≤
        scale * binomialKernel m ((k : ℤ) - j) (z / (1 + z)) wL wR wC) :
    KernelBudget.budget terms counts A B dδ dM α β D T rate U bound
        (hardCoreAvailableMean G S I z) ≤
      scale * averagedBinomialKernel G S I z wL wR wC k := by
  let Ω := range ((S \ I).card + 1) ×ˢ range (I.card + 1)
  let w : ℕ × ℕ → ℝ := fun p => hardCoreLayerWeight G S I z p.1 p.2
  let M : ℕ × ℕ → ℝ := fun p => (p.2 : ℝ)
  let δ : ℕ × ℕ → ℝ := fun p => (k : ℝ) - binomialLayerMean p.1 p.2 z
  let f : ℕ × ℕ → ℝ := fun p =>
    binomialKernel p.2 ((k : ℤ) - p.1) (z / (1 + z)) wL wR wC
  let lap : ι → ℕ × ℕ → ℝ := fun i p =>
    (1 - z / (1 + z) + z / (1 + z) * t i) ^ p.2
  let ct : ℤ → ℕ × ℕ → ℝ := fun r p =>
    if (k : ℤ) - p.1 = r then (1 - z / (1 + z)) ^ p.2 else 0
  have hw : ∀ p ∈ Ω, 0 ≤ w p := fun p _ => hardCoreLayerWeight_nonneg G S I hz.le p.1 p.2
  have hsum : ∑ p ∈ Ω, w p = 1 := by
    simpa only [Ω, w, sum_product] using sum_hardCoreLayerWeight G S I hIS hI hz.le
  have hm : KernelBudget.expect Ω w M = hardCoreAvailableMean G S I z := by
    simp only [KernelBudget.expect, Ω, w, M, sum_product, hardCoreAvailableMean]
  have hδ : KernelBudget.expect Ω w δ = 0 := by
    simpa only [hardCoreLayerExpectation_eq_expect, Ω, w, δ] using
      hardCoreLayerExpectation_centered_mean G S I hIS hI hz hmean
  have hδsq : KernelBudget.expect Ω w (fun p => δ p ^ 2) ≤
      α * hardCoreAvailableMean G S I z + β := by
    have heq := hardCoreLayerExpectation_centered_sq G S I hIS hI hz hmean
    rw [hardCoreLayerExpectation_eq_expect] at heq
    change KernelBudget.expect Ω w (fun p => δ p ^ 2) = _ at heq
    nlinarith
  have hvar : KernelBudget.expect Ω w
      (fun p => (M p - hardCoreAvailableMean G S I z) ^ 2) ≤
        D * hardCoreAvailableMean G S I z := by
    simpa only [hardCoreAvailableVariance, hardCoreLayerExpectation_eq_expect, Ω, w, M] using hvarM
  have hl : ∀ i ∈ terms, KernelBudget.expect Ω w (lap i) ≤
      Real.exp (-rate i * hardCoreAvailableMean G S I z) := by
    intro i hi
    simpa only [hardCoreLayerLaplace, hardCoreLayerExpectation_eq_expect, Ω, w, lap] using hlap i hi
  have hc : ∀ r ∈ counts, KernelBudget.expect Ω w (ct r) ≤ bound r := by
    intro r hr
    simpa only [hardCoreFixedShiftMass, hardCoreLayerExpectation_eq_expect, Ω, w, ct] using hcount r hr
  have hp : ∀ p ∈ Ω, 0 < w p →
      A + B * M p + C * δ p - dδ * δ p ^ 2 - dM * M p ^ 2 -
        (∑ i ∈ terms, T i * lap i p) - ∑ r ∈ counts, U r * ct r p ≤ scale * f p := by
    intro p hp hw
    exact hpoint p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2 hw
  have h := KernelBudget.budget_le_scaled_expect Ω w M δ f terms counts lap ct
    scale A B C dδ dM α β D (hardCoreAvailableMean G S I z) T rate U bound
    hw hsum hm hδ hdδ hdM hT hU hδsq hvar hl hc hp
  simpa only [KernelBudget.expect, Ω, w, f, sum_product, averagedBinomialKernel] using h

theorem averagedBinomialKernel_pos_of_budget {ι : Type*}
    (G : SimpleGraph V) (S I : Finset V) (z wL wR wC : ℝ) (k : ℕ)
    (terms : Finset ι) (counts : Finset ℤ)
    (scale A B dδ dM α β D : ℝ) (T rate : ι → ℝ) (U bound : ℤ → ℝ)
    (hscale : 0 < scale)
    (hbound : KernelBudget.budget terms counts A B dδ dM α β D T rate U bound
        (hardCoreAvailableMean G S I z) ≤ scale * averagedBinomialKernel G S I z wL wR wC k)
    (hbudget : 0 < KernelBudget.budget terms counts A B dδ dM α β D T rate U bound
        (hardCoreAvailableMean G S I z)) :
    0 < averagedBinomialKernel G S I z wL wR wC k := by
  exact (mul_pos_iff_of_pos_left hscale).mp (hbudget.trans_le hbound)

#print axioms hardCoreLayerExpectation_centered_mean
#print axioms hardCoreLayerExpectation_centered_sq
#print axioms averagedBinomialKernel_budget_lower
#print axioms averagedBinomialKernel_pos_of_budget
#print axioms KernelBudget.budget_pos_of_endpoints

end ForestUnimodality
