import ForestUnimodality.AffineSourceCertificate
import ForestUnimodality.SourceCertifiedLibrary
import ForestUnimodality.Stage900SourceTable

/-! Source improvements used at order 350. The marked source improves the
variance only at the actual activity. The affine source is separately valid
along the whole downward tilt of the same fixed set. -/
namespace ForestUnimodality.Stage350SourceBudget

noncomputable def affineCoefficient (A B q : ℝ) : ℝ := 1+B/q-A/q^2

theorem affineCoefficient_le_right {A B q r : ℝ}
    (hA : 0≤A) (hq : 0<q) (hqr : q≤r) (hBr : B*r≤2*A) :
    affineCoefficient A B q≤affineCoefficient A B r := by
  have hr := hq.trans_le hqr
  have hnum : 0≤A*(r+q)-B*q*r := by
    have h₁ := mul_nonneg hA (sub_nonneg.mpr hqr)
    have h₂ := mul_nonneg (sub_nonneg.mpr hBr) hq.le
    nlinarith
  have hf := div_nonneg (mul_nonneg (sub_nonneg.mpr hqr) hnum)
    (by positivity : 0≤q^2*r^2)
  have he : affineCoefficient A B r-affineCoefficient A B q =
      (r-q)*(A*(r+q)-B*q*r)/(q^2*r^2) := by
    unfold affineCoefficient
    field_simp
    ring
  linarith

theorem affineCoefficient_le_left {A B q r : ℝ}
    (hA : 0≤A) (hq : 0<q) (hqr : q≤r) (hBq : 2*A≤B*q) :
    affineCoefficient A B r≤affineCoefficient A B q := by
  have hr := hq.trans_le hqr
  have hnum : 0≤B*q*r-A*(q+r) := by
    have h₁ := mul_nonneg hA (sub_nonneg.mpr hqr)
    have h₂ := mul_nonneg (sub_nonneg.mpr hBq) hr.le
    nlinarith
  have hf := div_nonneg (mul_nonneg (sub_nonneg.mpr hqr) hnum)
    (by positivity : 0≤q^2*r^2)
  have he : affineCoefficient A B q-affineCoefficient A B r =
      (r-q)*(B*q*r-A*(q+r))/(q^2*r^2) := by
    unfold affineCoefficient
    field_simp
    ring
  linarith

structure MarkedRow where
  lower : ℚ
  upper : ℚ
  factor : ℚ

def markedRow (i : Fin 10) : MarkedRow :=
  ![⟨22/25,1,16391069/12500000⟩,
    ⟨1,11/10,66563367/50000000⟩,
    ⟨11/10,57/50,129553901/100000000⟩,
    ⟨7/10,22/25,66804403/50000000⟩,
    ⟨57/50,6/5,33494171/25000000⟩,
    ⟨6/5,13/10,7094721/5000000⟩,
    ⟨13/10,3/2,159655229/100000000⟩,
    ⟨3/2,9/5,45689627/25000000⟩,
    ⟨9/5,9/4,109621781/50000000⟩,
    ⟨53/50,57/50,66518673/50000000⟩] i

theorem markedRow_parameters (i : Fin 10) :
    0<(markedRow i).lower ∧ 1≤(markedRow i).factor := by
  fin_cases i <;> norm_num [markedRow]

variable {V : Type*} [DecidableEq V]

theorem marked_available_variance (i : Fin 10)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hlo : ((markedRow i).lower:ℝ)≤z) (hhi : z≤((markedRow i).upper:ℝ)) :
    hardCoreAvailableVariance G S B z ≤
      (1+(((markedRow i).factor:ℝ)-1)/(z/(1+z)))*hardCoreAvailableMean G S B z := by
  fin_cases i
  · norm_num [markedRow] at hlo hhi ⊢
    exact hB.available_variance_22_25_1 hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case02.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case03.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case04.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case05.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case06.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case07.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case08.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case09.available_variance hB hG hlo hhi
  · norm_num [markedRow] at hlo hhi ⊢
    exact ParametricSourceData.Case10.available_variance hB hG hlo hhi

theorem marked_available_variance_le (i : Fin 10)
    {G : SimpleGraph V} {S B : Finset V} {z qa D : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hlo : ((markedRow i).lower:ℝ)≤z) (hhi : z≤((markedRow i).upper:ℝ))
    (hqa : 0<qa) (hqaQ : qa≤z/(1+z))
    (hD : 1+(((markedRow i).factor:ℝ)-1)/qa≤D) :
    hardCoreAvailableVariance G S B z ≤ D*hardCoreAvailableMean G S B z := by
  have hp : (0:ℝ)<(markedRow i).lower := by exact_mod_cast (markedRow_parameters i).1
  have hz := hp.trans_le hlo
  have hn : 0≤((markedRow i).factor:ℝ)-1 := by
    have hh : (1:ℝ)≤(markedRow i).factor := by exact_mod_cast (markedRow_parameters i).2
    linarith
  have hc : 1+(((markedRow i).factor:ℝ)-1)/(z/(1+z))≤D :=
    (add_le_add le_rfl (div_le_div_of_nonneg_left hn hqa hqaQ)).trans hD
  exact (marked_available_variance i hB hG hlo hhi).trans
    (mul_le_mul_of_nonneg_right hc (hardCoreAvailableMean_nonneg G S B hz.le))

/-- A certified old affine source supplies the improved variance coefficient
using the actual density of the original graph at the same activity. -/
theorem affine_available_variance_le
    {G : SimpleGraph V} {S B : Finset V} {z b ρ qa qb D : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hzb : z≤b) (hρ : 0<ρ) (hρq : ρ≤z/(1+z))
    (hdensity : ρ*(S.card:ℝ)≤hardCoreMean G S z)
    (P : AffineSourceParameters) (hP : P.Admissible) (hA : 0≤P.A)
    (hvalid : AffineSourceRowValid P b) (hqa : 0<qa)
    (hq : z/(1+z)∈Set.Icc qa qb)
    (hbound :
      ((2*P.A/ρ+P.C-1)*qb≤2*P.A ∧ affineCoefficient P.A (2*P.A/ρ+P.C-1) qb≤D) ∨
      (2*P.A≤(2*P.A/ρ+P.C-1)*qa ∧ affineCoefficient P.A (2*P.A/ρ+P.C-1) qa≤D)) :
    hardCoreAvailableVariance G S B z≤D*hardCoreAvailableMean G S B z := by
  have hs := hB.available_variance_le_affine_density hG hz hρ hρq hA hdensity
    (hardCoreMarkedVariance_le_affine_source_certificate G hG S B hB.subset hz hzb P hP hvalid)
  have hc : affineCoefficient P.A (2*P.A/ρ+P.C-1) (z/(1+z))≤D := by
    rcases hbound with h | h
    · exact (affineCoefficient_le_right hA (hqa.trans_le hq.1) hq.2 h.1).trans h.2
    · exact (affineCoefficient_le_left hA hqa hq.1 h.1).trans h.2
  exact hs.trans (mul_le_mul_of_nonneg_right hc (hardCoreAvailableMean_nonneg G S B hz.le))

#print axioms marked_available_variance_le
#print axioms affine_available_variance_le
end ForestUnimodality.Stage350SourceBudget
