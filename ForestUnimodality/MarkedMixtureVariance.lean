import ForestUnimodality.HeterogeneousHardCore
import ForestUnimodality.MarginalIndependent

/-! The variance of occupation in a fixed independent set is the actual
conditional-binomial variance plus q² times the variance of availability.
All moments below use the original hard-core law and the same fixed set. -/
namespace ForestUnimodality
open Finset
open scoped Topology
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem powerset_moment_deriv (A : Finset V) (d : ℕ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => ∑ T ∈ A.powerset, (T.card : ℝ)^d * x^T.card)
      ((∑ T ∈ A.powerset, (T.card : ℝ)^(d+1) * z^T.card) / z) z := by
  classical
  have hd := HasDerivAt.fun_sum (u := A.powerset)
    (fun T _ => (hasDerivAt_pow T.card z).const_mul ((T.card : ℝ)^d))
  apply hd.congr_deriv
  rw [sum_div]
  apply sum_congr rfl
  intro T _
  cases hc : T.card with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one, pow_succ]; field_simp

omit [DecidableEq V] in
theorem sum_powerset_card_mul_pow (A : Finset V) {z : ℝ} (hz : 0 < z) :
    (∑ T ∈ A.powerset, (T.card : ℝ) * z^T.card) =
      (1+z)^A.card * (z/(1+z)*(A.card : ℝ)) := by
  have hfun : (fun x : ℝ => ∑ T ∈ A.powerset, (T.card : ℝ)^0 * x^T.card) =
      (fun x : ℝ => x^0 * (1+x)^A.card) := by
    funext x
    simpa using sum_powerset_pow_card A x
  have hd := powerset_moment_deriv A 0 (ne_of_gt hz)
  rw [hfun] at hd
  have he := hd.unique (hasDerivAt_binomial_block 0 A.card hz)
  simp only [zero_add, pow_one, pow_zero, one_mul, binomialLayerMean, Nat.cast_zero] at he
  exact (div_left_inj' (ne_of_gt hz)).mp he

omit [DecidableEq V] in
theorem sum_powerset_card_sq_mul_pow (A : Finset V) {z : ℝ} (hz : 0 < z) :
    (∑ T ∈ A.powerset, (T.card : ℝ)^2 * z^T.card) =
      (1+z)^A.card * ((z/(1+z)*(A.card : ℝ))^2 +
        z/(1+z)*(1-z/(1+z))*(A.card : ℝ)) := by
  have hevent : (fun x : ℝ => ∑ T ∈ A.powerset, (T.card : ℝ)^1 * x^T.card) =ᶠ[𝓝 z]
      (fun x : ℝ => x^0 * (1+x)^A.card * binomialLayerMean 0 A.card x) := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    simpa [binomialLayerMean] using sum_powerset_card_mul_pow A hx
  have hd := (hasDerivAt_binomial_block_first_moment 0 A.card hz).congr_of_eventuallyEq hevent
  have he := (powerset_moment_deriv A 1 (ne_of_gt hz)).unique hd
  simp only [pow_zero, one_mul, binomialLayerMean, binomialLayerVariance,
    Nat.cast_zero, zero_add] at he
  exact (div_left_inj' (ne_of_gt hz)).mp he

noncomputable def hardCoreMarkedVariance (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) : ℝ := heterogeneousVariance G S (fun _ => z) (fun J => ((J ∩ I).card : ℝ))

theorem hardCoreMarkedVariance_eq_second_sub_mass_sq (G : SimpleGraph V)
    (S I : Finset V) (z : ℝ) :
    hardCoreMarkedVariance G S I z =
      (∑ J ∈ independentSubsets G S, ((J ∩ I).card : ℝ)^2 * z^J.card) /
        partitionFunction G S z - hardCoreOccupiedMass G S I z ^ 2 := by
  rw [hardCoreOccupiedMass_eq_intersection_expectation]
  simp only [hardCoreMarkedVariance, heterogeneousVariance, FiniteTilt.variance,
    FiniteTilt.covariance, FiniteTilt.mean, FiniteTilt.numerator, FiniteTilt.total,
    heterogeneousWeight, prod_const, partitionFunction]
  congr 1 <;> simp only [pow_two, mul_comm]

theorem hardCoreMarkedSecond_eq_layer_second (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) :
    (∑ K ∈ independentSubsets G S, ((K ∩ I).card : ℝ)^2 * z^K.card) /
        partitionFunction G S z =
      hardCoreLayerExpectation G S I z (fun _ m =>
        (z/(1+z)*(m : ℝ))^2 + z/(1+z)*(1-z/(1+z))*(m : ℝ)) := by
  classical
  have hsplit : (∑ K ∈ independentSubsets G S, ((K ∩ I).card : ℝ)^2 * z^K.card) =
      ∑ J ∈ independentSubsets G (S \ I), z^J.card *
        ((1+z)^(available G I J).card *
          ((z/(1+z)*((available G I J).card : ℝ))^2 +
            z/(1+z)*(1-z/(1+z))*((available G I J).card : ℝ))) := by
    calc
      _ = ∑ K ∈ independentSubsets G S,
          ((K ∩ I).card : ℝ)^2 * z^((K \ I).card + (K ∩ I).card) := by
        apply sum_congr rfl
        intro K _
        rw [← split_card K I]
      _ = ∑ J ∈ independentSubsets G (S \ I),
          ∑ T ∈ (available G I J).powerset, (T.card : ℝ)^2 * z^(J.card+T.card) :=
        sum_independent_split_statistic G S I hIS hI
          (fun J T => (T.card : ℝ)^2 * z^(J.card+T.card))
      _ = _ := by
        apply sum_congr rfl
        intro J _
        simp_rw [pow_add, mul_left_comm (_ : ℝ) (z^J.card), ← mul_sum]
        rw [sum_powerset_card_sq_mul_pow _ hz]
  rw [hsplit, sum_independentSubsets_by_layers G I (S \ I)
    (fun j m => z^j * ((1+z)^m * ((z/(1+z)*(m : ℝ))^2 +
      z/(1+z)*(1-z/(1+z))*(m : ℝ))))]
  simp only [sum_div, hardCoreLayerExpectation, hardCoreLayerWeight]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  ring

theorem hardCoreAvailable_second_moment (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreLayerExpectation G S I z (fun _ m => (m : ℝ)^2) =
      hardCoreAvailableMean G S I z ^ 2 + hardCoreAvailableVariance G S I z := by
  have he := KernelBudget.second_moment_eq
    (range ((S \ I).card+1) ×ˢ range (I.card+1))
    (fun p => hardCoreLayerWeight G S I z p.1 p.2) (fun p => (p.2 : ℝ))
    (by simpa only [sum_product] using sum_hardCoreLayerWeight G S I hIS hI hz)
    (m := hardCoreAvailableMean G S I z)
    (by simp only [KernelBudget.expect, sum_product, hardCoreAvailableMean])
  simpa only [KernelBudget.expect, sum_product, hardCoreLayerExpectation,
    hardCoreAvailableVariance] using he

/-- Exact law of total variance, with the same graph, activity and fixed
independent set in both terms. No independence of the layer indices is used. -/
theorem hardCoreMarkedVariance_eq_available_variance (G : SimpleGraph V)
    (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z : ℝ} (hz : 0 < z) :
    hardCoreMarkedVariance G S I z =
      (z/(1+z))*(1-z/(1+z))*hardCoreAvailableMean G S I z +
      (z/(1+z))^2 * hardCoreAvailableVariance G S I z := by
  rw [hardCoreMarkedVariance_eq_second_sub_mass_sq,
    hardCoreMarkedSecond_eq_layer_second G S I hIS hI hz,
    hardCoreOccupiedMass_eq_activity_available_mean G S I hIS hI hz]
  have hpoint (j m : ℕ) : hardCoreLayerWeight G S I z j m *
      ((z/(1+z)*(m : ℝ))^2 + z/(1+z)*(1-z/(1+z))*(m : ℝ)) =
        (z/(1+z))^2 * (hardCoreLayerWeight G S I z j m * (m : ℝ)^2) +
        (z/(1+z)*(1-z/(1+z))) * (hardCoreLayerWeight G S I z j m * (m : ℝ)) := by ring
  simp only [hardCoreLayerExpectation, hpoint, sum_add_distrib, ← mul_sum]
  change (z/(1+z))^2 * hardCoreLayerExpectation G S I z (fun _ m => (m : ℝ)^2) +
    (z/(1+z)*(1-z/(1+z))) * hardCoreAvailableMean G S I z -
      (z/(1+z)*hardCoreAvailableMean G S I z)^2 = _
  rw [hardCoreAvailable_second_moment G S I hIS hI hz.le]
  ring

theorem hardCoreAvailableVariance_eq_marked (G : SimpleGraph V)
    (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z : ℝ} (hz : 0 < z) :
    hardCoreAvailableVariance G S I z =
      (hardCoreMarkedVariance G S I z -
        (1-z/(1+z))*hardCoreOccupiedMass G S I z) / (z/(1+z))^2 := by
  rw [hardCoreMarkedVariance_eq_available_variance G S I hIS hI hz,
    hardCoreOccupiedMass_eq_activity_available_mean G S I hIS hI hz]
  have hq : z/(1+z) ≠ 0 := ne_of_gt (by positivity : 0 < z/(1+z))
  field_simp
  ring

/-- A source bound on occupation variance becomes the precise available
variance bound used by the kernel budgets. The maximizing set is unchanged. -/
theorem IsMaximumMarginalIndependentOn.available_variance_le_of_marked
    {G : SimpleGraph V} {S I : Finset V} {z A C : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hA : 0 ≤ A)
    (hsource : hardCoreMarkedVariance G S I z ≤
      A * hardCoreMean G S z + C * hardCoreOccupiedMass G S I z) :
    hardCoreAvailableVariance G S I z ≤
      (1 + (2*A+C-1)/(z/(1+z))) * hardCoreAvailableMean G S I z := by
  have hhalf := hI.half_mean hG.isBipartite
  have hAhalf := mul_le_mul_of_nonneg_left hhalf hA
  have hv := hardCoreMarkedVariance_eq_available_variance G S I hI.subset hI.independent hz
  have hmass := hardCoreOccupiedMass_eq_activity_available_mean G S I hI.subset hI.independent hz
  have hq : 0 < z/(1+z) := by positivity
  have hbound : (z/(1+z))^2 * hardCoreAvailableVariance G S I z ≤
      (z/(1+z)) * ((z/(1+z)) + 2*A+C-1) * hardCoreAvailableMean G S I z := by
    rw [hmass] at hsource hAhalf
    nlinarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hq)).mp
  calc
    (z/(1+z))^2 * hardCoreAvailableVariance G S I z ≤
        (z/(1+z)) * ((z/(1+z)) + 2*A+C-1) * hardCoreAvailableMean G S I z := hbound
    _ = (z/(1+z))^2 *
        ((1 + (2*A+C-1)/(z/(1+z))) * hardCoreAvailableMean G S I z) := by
      field_simp
      ring

#print axioms hardCoreMarkedSecond_eq_layer_second
#print axioms hardCoreMarkedVariance_eq_available_variance
#print axioms IsMaximumMarginalIndependentOn.available_variance_le_of_marked
end ForestUnimodality
