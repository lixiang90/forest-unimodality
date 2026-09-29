import ForestUnimodality.Stage59KernelData.Cell164.Parameters
import ForestUnimodality.ActivityPointDensityData.Point076
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.Stage59KernelData.Cell164.RankLower
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def factor : ℚ := (1/1)

theorem activity_lower {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) : (activityLower:ℝ)≤z := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  norm_num [interval,activityLower] at hl ⊢
  linarith

theorem checked :
    0<ActivityPointDensityData.Point076.certificate.parameters.x ∧ ActivityPointDensityData.Point076.certificate.parameters.x≤activityLower ∧
    0≤factor ∧ factor^2*ActivityPointDensityData.Point076.certificate.parameters.x*(1+activityLower)≤
      activityLower*(1+ActivityPointDensityData.Point076.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point076.certificate.parameters.r ∧
    (17:ℚ)<factor*(ActivityPointDensityData.Point076.certificate.parameters.r*59+ActivityPointDensityData.Point076.certificate.parameters.h) := by
  decide +kernel

theorem actual_rank (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hn : 59≤S.card) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (k : ℕ) (hmean : hardCoreMean G S z=k) : 18≤k := by
  rcases checked with ⟨hx,hxa,hg,hfactor,hr,hthreshold⟩
  have hd := ActivityPointDensity.Certificate.transferred_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point076.checked)
    G hG S (by omega) (a:=(activityLower:ℝ)) (gamma:=(factor:ℝ))
    (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_lower hz hq)
    (by exact_mod_cast hg) (by exact_mod_cast hfactor)
  have hnR : (59:ℝ)≤S.card := by exact_mod_cast hn
  have hrR : (0:ℝ)≤ActivityPointDensityData.Point076.certificate.parameters.r := by exact_mod_cast hr
  have hgR : (0:ℝ)≤factor := by exact_mod_cast hg
  have hmono := mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left hnR hrR) (ActivityPointDensityData.Point076.certificate.parameters.h:ℝ)) hgR
  have hthresholdR : (17:ℝ)<(factor:ℝ)*
      ((ActivityPointDensityData.Point076.certificate.parameters.r:ℝ)*59+ActivityPointDensityData.Point076.certificate.parameters.h) := by exact_mod_cast hthreshold
  rw [hmean] at hd
  by_contra hk
  have hupper : (k:ℝ)≤17 := by exact_mod_cast (show k≤17 by omega)
  linarith

#print axioms activity_lower
#print axioms checked
#print axioms actual_rank
end ForestUnimodality.Stage59KernelData.Cell164.RankLower
