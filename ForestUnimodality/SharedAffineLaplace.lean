import ForestUnimodality.AffineSourceLaplaceRate

/-! A shared exponential enclosure suffices for every zero-threshold affine
Laplace rate. Each new interval checks only rational endpoint inequalities;
no logarithm enclosure or repeated Taylor reduction is needed. -/
namespace ForestUnimodality.SharedAffineLaplace

def lowerRate (A C density u q decayUpper : ℚ) : ℚ :=
  q*((1-decayUpper)/C)-A/C*(2*q/density-1)*(u-(1-decayUpper)/C)

def EndpointAccepts (A C density u q rate decayUpper : ℚ) : Prop :=
  0≤A ∧ 0<C ∧ 0<density ∧ 0≤q ∧ density≤2*q ∧
    rate≤lowerRate A C density u q decayUpper

instance (A C density u q rate decayUpper : ℚ) :
    Decidable (EndpointAccepts A C density u q rate decayUpper) := by
  unfold EndpointAccepts
  infer_instance

theorem endpoint_sound {A C density u q rate decayUpper : ℚ}
    (h : EndpointAccepts A C density u q rate decayUpper)
    (he : Real.exp (-(C:ℝ)*(u:ℝ)) ≤ (decayUpper:ℝ)) :
    (rate:ℝ) ≤ AffineLaplace.tailRate A C density 0 u q := by
  rcases h with ⟨hA,hC,hd,hq,hdq,hr⟩
  have hA' : (0:ℝ)≤A := by exact_mod_cast hA
  have hC' : (0:ℝ)<C := by exact_mod_cast hC
  have hd' : (0:ℝ)<density := by exact_mod_cast hd
  have hq' : (0:ℝ)≤q := by exact_mod_cast hq
  have hdq' : (density:ℝ)≤2*q := by exact_mod_cast hdq
  have hf : (1-(decayUpper:ℝ))/C≤AffineLaplace.decayIntegral C u := by
    unfold AffineLaplace.decayIntegral
    exact div_le_div_of_nonneg_right (sub_le_sub_left he 1) hC'.le
  have hcoef : 0≤(A:ℝ)/C*(2*q/density-1) := by
    apply mul_nonneg (div_nonneg hA' hC'.le)
    have hh : (1:ℝ)≤2*q/density := (le_div_iff₀ hd').mpr (by simpa using hdq')
    linarith
  have hr' : (rate:ℝ)≤lowerRate A C density u q decayUpper := by exact_mod_cast hr
  simp only [lowerRate, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hr'
  apply hr'.trans
  simpa only [AffineLaplace.tailRate, zero_mul, add_zero] using
    sub_le_sub (mul_le_mul_of_nonneg_left hf hq')
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hf (u:ℝ)) hcoef)

variable {V : Type*} [DecidableEq V]

theorem actual_laplace (i : Fin 15) {ρ u qa qb retention rate decayUpper : ℚ}
    (hu : 0≤u) (ht : 0≤retention) (hqb : qb≤1)
    (he : (retention:ℝ)≤Real.exp (-(u:ℝ)))
    (hc : Real.exp (-((AffineSourceLibrary.parameters i).C:ℝ)*(u:ℝ))≤(decayUpper:ℝ))
    (hlo : EndpointAccepts (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C ρ u qa rate decayUpper)
    (hhi : EndpointAccepts (AffineSourceLibrary.parameters i).A
      (AffineSourceLibrary.parameters i).C ρ u qb rate decayUpper)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤((AffineSourceLibrary.domain i).b:ℝ))
    (hS : 0<S.card) (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (ρ:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤
      Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hρ : (0:ℝ)<ρ := by exact_mod_cast hlo.2.2.1
  apply (hardCoreLayerLaplace_mono G S B hz.le (by exact_mod_cast ht) he).trans
  exact hB.laplace_le_affine_source_rate hG i hz hzb hρ
    (MeanMatchedSourceBudget.density_le_probability_cap G S hz hS hdensity)
    (by exact_mod_cast hu) hdensity (by exact_mod_cast hlo.2.2.2.1)
    (by exact_mod_cast hqb) hq (endpoint_sound hlo hc) (endpoint_sound hhi hc)

#print axioms endpoint_sound
#print axioms actual_laplace
end ForestUnimodality.SharedAffineLaplace
