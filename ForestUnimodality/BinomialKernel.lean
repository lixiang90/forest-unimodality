import ForestUnimodality.HardCoreMixture
import ForestUnimodality.AnalyticAssembly

/-! Signed finite binomial kernels and their exact interpretation for the
same hard-core mixture. A positive kernel average excludes a coefficient
valley; this does not assert positivity of unverified certificate data. -/

namespace ForestUnimodality
open Finset

noncomputable def binomialKernel (m : ℕ) (j : ℤ) (q wL wR wC : ℝ) : ℝ :=
  wL * ((1 - q) * binomialMass m j q - q * binomialMass m (j - 1) q) +
  wR * (q * binomialMass m j q - (1 - q) * binomialMass m (j + 1) q) +
  wC * (2 * binomialMass m j q - binomialMass m (j - 1) q - binomialMass m (j + 1) q)

variable {V : Type*} [DecidableEq V]

noncomputable def averagedBinomialKernel (G : SimpleGraph V) (S I : Finset V)
    (z wL wR wC : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
    hardCoreLayerWeight G S I z j m *
      binomialKernel m ((k : ℤ) - j) (z / (1 + z)) wL wR wC

theorem averagedBinomialKernel_eq (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z : ℝ} (hz : 0 < z) (wL wR wC : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    averagedBinomialKernel G S I z wL wR wC k =
      wL * tiltedLeft (countIndependent G S) z (partitionFunction G S z) k +
      wR * tiltedRight (countIndependent G S) z (partitionFunction G S z) k +
      wC * tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  have hprev : ∀ j : ℕ, (k : ℤ) - j - 1 = ((k - 1 : ℕ) : ℤ) - j := by
    intro j
    omega
  have hnext : ∀ j : ℕ, (k : ℤ) - j + 1 = ((k + 1 : ℕ) : ℤ) - j := by
    intro j
    omega
  simp only [averagedBinomialKernel, binomialKernel, hprev, hnext,
    tiltedLeft, tiltedRight, tiltedCenter,
    tiltedProbability_eq_binomial_mixture G S I hIS hI hz]
  simp only [mul_add, mul_sub, mul_sum, sum_add_distrib, sum_sub_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- The forest assumption and choice of a special independent set are not
needed for this exact interpretation; those enter the positivity estimates. -/
theorem no_weak_valley_of_positive_binomial_kernel (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z wL wR wC : ℝ} (hz : 0 < z)
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hwC : 0 ≤ wC)
    {k : ℕ} (hk : 1 ≤ k) (hpositive : 0 < averagedBinomialKernel G S I z wL wR wC k) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k - 1) ∧
      countIndependent G S k ≤ countIndependent G S (k + 1)) := by
  rw [averagedBinomialKernel_eq G S I hIS hI hz wL wR wC hk] at hpositive
  exact no_weak_valley_of_positive_tilted_kernel (countIndependent G S) hz
    (partitionFunction_pos G S hz.le) hwL hwR hwC hk hpositive

/-- Conditional graph assembly with every remaining analytic obligation
visible: the initial/tail bounds and a positive actual kernel at each central
rank. No claim that arbitrary forests satisfy these hypotheses is made here. -/
theorem countIndependent_unimodal_of_binomial_kernel_bounds
    (G : SimpleGraph V) (S : Finset V) (L U : ℕ)
    (hbefore : ∀ k < L, countIndependent G S k ≤ countIndependent G S (k + 1))
    (hafter : ∀ k, U ≤ k → countIndependent G S (k + 1) ≤ countIndependent G S k)
    (hpositive : ∀ k, L ≤ k → k < U → 1 ≤ k →
      ∃ (I : Finset V) (z wL wR wC : ℝ),
        I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧ 0 < z ∧
        0 ≤ wL ∧ 0 ≤ wR ∧ 0 ≤ wC ∧ 0 < averagedBinomialKernel G S I z wL wR wC k) :
    WeaklyUnimodal (countIndependent G S) := by
  apply weaklyUnimodal_of_no_central_weak_valley (countIndependent G S) L U hbefore hafter
  intro k hkL hkU hk
  obtain ⟨I, z, wL, wR, wC, hIS, hI, hz, hwL, hwR, hwC, hpos⟩ := hpositive k hkL hkU hk
  exact no_weak_valley_of_positive_binomial_kernel G S I hIS hI hz hwL hwR hwC hk hpos

#print axioms averagedBinomialKernel_eq
#print axioms no_weak_valley_of_positive_binomial_kernel
#print axioms countIndependent_unimodal_of_binomial_kernel_bounds

end ForestUnimodality
