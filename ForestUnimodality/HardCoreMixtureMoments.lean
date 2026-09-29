import ForestUnimodality.HardCoreMixture
import Mathlib.Algebra.BigOperators.Field

/-! Actual first and second moments of the graph's binomial mixture. We
differentiate the proved finite partition-function decomposition, then use
uniqueness of the already proved derivatives of the graph moment numerators.
No moment or conditional-variance identity is assumed. -/

namespace ForestUnimodality
open Finset
open scoped Topology

noncomputable def binomialLayerMean (j m : ℕ) (z : ℝ) : ℝ :=
  (j : ℝ) + z / (1 + z) * (m : ℝ)

noncomputable def binomialLayerVariance (m : ℕ) (z : ℝ) : ℝ :=
  (z / (1 + z)) * (1 - z / (1 + z)) * (m : ℝ)

private theorem hasDerivAt_pow_log_form (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => y ^ n) ((n : ℝ) * x ^ n / x) x := by
  have heq : (n : ℝ) * x ^ (n - 1) = (n : ℝ) * x ^ n / x := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, pow_succ]; field_simp
  rw [← heq]
  exact hasDerivAt_pow n x

theorem hasDerivAt_binomial_block (j m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => x ^ j * (1 + x) ^ m)
      (z ^ j * (1 + z) ^ m * binomialLayerMean j m z / z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hb : 1 + z ≠ 0 := by positivity
  have h1 := hasDerivAt_pow_log_form j hzne
  have h2 : HasDerivAt (fun x : ℝ => (1 + x) ^ m)
      ((m : ℝ) * (1 + z) ^ m / (1 + z)) z := by
    simpa only [Function.comp_def, mul_one] using
      (hasDerivAt_pow_log_form m hb).comp z ((hasDerivAt_id z).const_add 1)
  apply (h1.mul h2).congr_deriv
  dsimp [binomialLayerMean]
  field_simp

theorem hasDerivAt_binomialLayerMean (j m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (binomialLayerMean j m) (binomialLayerVariance m z / z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hb : 1 + z ≠ 0 := by positivity
  have hd := (((hasDerivAt_id z).div ((hasDerivAt_id z).const_add 1) hb).mul_const
    (m : ℝ)).const_add (j : ℝ)
  apply hd.congr_deriv
  dsimp [binomialLayerVariance]
  field_simp

theorem hasDerivAt_binomial_block_first_moment (j m : ℕ)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => x ^ j * (1 + x) ^ m * binomialLayerMean j m x)
      (z ^ j * (1 + z) ^ m *
        (binomialLayerMean j m z ^ 2 + binomialLayerVariance m z) / z) z := by
  apply ((hasDerivAt_binomial_block j m hz).mul
    (hasDerivAt_binomialLayerMean j m hz)).congr_deriv
  ring

variable {V : Type*} [DecidableEq V]

/-- Grouping the graph's independent subsets by their actual cardinality
identifies its moment numerator with the cardinality probability numerator. -/
theorem hardCoreMomentNumerator_eq_cardinality_sum (G : SimpleGraph V) (S : Finset V)
    (d : ℕ) (z : ℝ) :
    hardCoreMomentNumerator G S d z =
      ∑ k ∈ range (S.card + 1), (countIndependent G S k : ℝ) * (k : ℝ) ^ d * z ^ k := by
  classical
  have hcover : ∀ J ∈ independentSubsets G S, J.card ∈ range (S.card + 1) := by
    intro J hJ
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_independentSubsets.mp hJ).1))
  rw [hardCoreMomentNumerator,
    ← sum_fiberwise_of_maps_to hcover (fun J : Finset V => (J.card : ℝ) ^ d * z ^ J.card)]
  apply sum_congr rfl
  intro k _
  calc
    (∑ J ∈ (independentSubsets G S).filter (fun J => J.card = k),
        (J.card : ℝ) ^ d * z ^ J.card) =
      ∑ _J ∈ (independentSubsets G S).filter (fun J => J.card = k), (k : ℝ) ^ d * z ^ k := by
        apply sum_congr rfl
        intro J hJ
        rw [(mem_filter.mp hJ).2]
    _ = _ := by simp [countIndependent, nsmul_eq_mul, mul_assoc]

theorem hardCoreMean_eq_cardinality_expectation (G : SimpleGraph V) (S : Finset V)
    (z : ℝ) :
    hardCoreMean G S z =
      ∑ k ∈ range (S.card + 1), (k : ℝ) *
        tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  rw [hardCoreMean, hardCoreMomentNumerator_eq_cardinality_sum]
  simp only [sum_div, pow_one, tiltedProbability]
  apply sum_congr rfl
  intro k _
  ring

theorem hardCoreSecondMoment_eq_cardinality_expectation (G : SimpleGraph V)
    (S : Finset V) (z : ℝ) :
    hardCoreSecondMoment G S z =
      ∑ k ∈ range (S.card + 1), (k : ℝ) ^ 2 *
        tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  rw [hardCoreSecondMoment, hardCoreMomentNumerator_eq_cardinality_sum]
  simp only [sum_div, tiltedProbability]
  apply sum_congr rfl
  intro k _
  ring

theorem hardCore_first_numerator_eq_layer_sum (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreMomentNumerator G S 1 z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : ℝ) *
          (z ^ j * (1 + z) ^ m * binomialLayerMean j m z) := by
  have hd := HasDerivAt.fun_sum (u := range ((S \ I).card + 1)) (fun j _ =>
    HasDerivAt.fun_sum (u := range (I.card + 1)) (fun m _ =>
      (hasDerivAt_binomial_block j m hz).const_mul (layerCount G I (S \ I) j m : ℝ)))
  have hfun : (fun x : ℝ => partitionFunction G S x) =
      (fun x => ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : ℝ) * (x ^ j * (1 + x) ^ m)) := by
    funext x
    simpa only [mul_assoc] using partitionFunction_layer_decomposition G S I hIS hI x
  have hdG := hasDerivAt_partitionFunction G S (ne_of_gt hz)
  rw [hfun] at hdG
  have heq := hdG.unique hd
  simp only [← mul_div_assoc, ← sum_div] at heq
  exact (div_left_inj' (ne_of_gt hz)).mp heq

theorem hardCoreMean_eq_layer_mean (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreMean G S z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        hardCoreLayerWeight G S I z j m * binomialLayerMean j m z := by
  rw [hardCoreMean, hardCore_first_numerator_eq_layer_sum G S I hIS hI hz]
  simp only [sum_div, hardCoreLayerWeight]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  ring

theorem hardCore_second_numerator_eq_layer_sum (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreMomentNumerator G S 2 z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : ℝ) *
          (z ^ j * (1 + z) ^ m *
            (binomialLayerMean j m z ^ 2 + binomialLayerVariance m z)) := by
  have hd := HasDerivAt.fun_sum (u := range ((S \ I).card + 1)) (fun j _ =>
    HasDerivAt.fun_sum (u := range (I.card + 1)) (fun m _ =>
      (hasDerivAt_binomial_block_first_moment j m hz).const_mul
        (layerCount G I (S \ I) j m : ℝ)))
  have hevent : hardCoreMomentNumerator G S 1 =ᶠ[𝓝 z]
      (fun x => ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : ℝ) *
          (x ^ j * (1 + x) ^ m * binomialLayerMean j m x)) := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    exact hardCore_first_numerator_eq_layer_sum G S I hIS hI hx
  have hd' := hd.congr_of_eventuallyEq hevent
  have heq := (hasDerivAt_hardCoreMomentNumerator G S 1 (ne_of_gt hz)).unique hd'
  simp only [← mul_div_assoc, ← sum_div] at heq
  exact (div_left_inj' (ne_of_gt hz)).mp heq

theorem hardCoreSecondMoment_eq_layer_second_moment (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreSecondMoment G S z =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        hardCoreLayerWeight G S I z j m *
          (binomialLayerMean j m z ^ 2 + binomialLayerVariance m z) := by
  rw [hardCoreSecondMoment, hardCore_second_numerator_eq_layer_sum G S I hIS hI hz]
  simp only [sum_div, hardCoreLayerWeight]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  ring

/-- The expected number of available vertices in the fixed independent set,
under the actual layer weights. -/
noncomputable def hardCoreAvailableMean (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) : ℝ :=
  ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
    hardCoreLayerWeight G S I z j m * (m : ℝ)

/-- The layerwise mean's squared deviation from the actual graph mean. -/
noncomputable def hardCoreLayerMeanVariance (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) : ℝ :=
  ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
    hardCoreLayerWeight G S I z j m *
      (binomialLayerMean j m z - hardCoreMean G S z) ^ 2

theorem hardCoreLayerMeanVariance_nonneg (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hardCoreLayerMeanVariance G S I z := by
  exact sum_nonneg fun j _ => sum_nonneg fun m _ =>
    mul_nonneg (hardCoreLayerWeight_nonneg G S I hz j m) (sq_nonneg _)

theorem hardCoreLayerMeanVariance_eq_second_sub_mean_sq
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreLayerMeanVariance G S I z =
      (∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        hardCoreLayerWeight G S I z j m * binomialLayerMean j m z ^ 2) -
      hardCoreMean G S z ^ 2 := by
  unfold hardCoreLayerMeanVariance
  have hpoint (j m : ℕ) :
      hardCoreLayerWeight G S I z j m *
          (binomialLayerMean j m z - hardCoreMean G S z) ^ 2 =
        hardCoreLayerWeight G S I z j m * binomialLayerMean j m z ^ 2 -
        (2 * hardCoreMean G S z) *
          (hardCoreLayerWeight G S I z j m * binomialLayerMean j m z) +
        hardCoreMean G S z ^ 2 * hardCoreLayerWeight G S I z j m := by ring
  simp_rw [hpoint]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [← hardCoreMean_eq_layer_mean G S I hIS hI hz, sum_hardCoreLayerWeight G S I hIS hI hz.le]
  ring

/-- Law of total variance for the actual hard-core cardinality distribution.
The conditional mean and variance are proved from the graph decomposition;
no forest, maximum-independent-set, or probabilistic identity is assumed. -/
theorem hardCoreVariance_eq_layer_variance (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    hardCoreVariance G S z =
      (z / (1 + z)) * (1 - z / (1 + z)) * hardCoreAvailableMean G S I z +
        hardCoreLayerMeanVariance G S I z := by
  rw [hardCoreVariance, hardCoreSecondMoment_eq_layer_second_moment G S I hIS hI hz,
    hardCoreLayerMeanVariance_eq_second_sub_mean_sq G S I hIS hI hz]
  simp only [mul_add, sum_add_distrib]
  have hnoise : (∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
      hardCoreLayerWeight G S I z j m * binomialLayerVariance m z) =
      (z / (1 + z)) * (1 - z / (1 + z)) * hardCoreAvailableMean G S I z := by
    simp only [hardCoreAvailableMean, binomialLayerVariance, mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro m _
    ring
  rw [hnoise]
  ring

/-- Every independent subset gives this lower bound on the graph's true
variance. Bipartite or maximum-independent-set choices can specialize it. -/
theorem hardCoreVariance_ge_binomial_available_mean
    (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    (z / (1 + z)) * (1 - z / (1 + z)) * hardCoreAvailableMean G S I z ≤
      hardCoreVariance G S z := by
  rw [hardCoreVariance_eq_layer_variance G S I hIS hI hz]
  exact le_add_of_nonneg_right (hardCoreLayerMeanVariance_nonneg G S I hz.le)

#print axioms hardCoreMean_eq_layer_mean
#print axioms hardCoreSecondMoment_eq_layer_second_moment
#print axioms hardCoreVariance_eq_layer_variance
#print axioms hardCoreVariance_ge_binomial_available_mean
#print axioms hardCoreMomentNumerator_eq_cardinality_sum
#print axioms hardCoreMean_eq_cardinality_expectation
#print axioms hardCoreSecondMoment_eq_cardinality_expectation

end ForestUnimodality
