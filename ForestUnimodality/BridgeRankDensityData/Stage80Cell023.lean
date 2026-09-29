import ForestUnimodality.Stage80KernelData.Cell023.Parameters
import ForestUnimodality.ActivityPointDensityData.Point012
import ForestUnimodality.ActivityPointDensityTransfer

namespace ForestUnimodality.BridgeRankDensityData.Stage80Cell023
open Stage80KernelData.Cell023
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def activityLower : ℚ := (65/88)
def transferFactor : ℚ := (1/1)

theorem activity_lower {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    (activityLower:ℝ)≤z := by
  have hl := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  norm_num [interval,activityLower] at hl ⊢
  linarith

theorem rank_checked :
    0<ActivityPointDensityData.Point012.certificate.parameters.x ∧ ActivityPointDensityData.Point012.certificate.parameters.x≤activityLower ∧
    0≤transferFactor ∧ transferFactor^2*ActivityPointDensityData.Point012.certificate.parameters.x*(1+activityLower)≤
      activityLower*(1+ActivityPointDensityData.Point012.certificate.parameters.x) ∧
    0≤ActivityPointDensityData.Point012.certificate.parameters.r ∧
    (20:ℚ)<transferFactor*(ActivityPointDensityData.Point012.certificate.parameters.r*80+ActivityPointDensityData.Point012.certificate.parameters.h) := by
  decide +kernel

theorem rank_lower (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hn : 80≤S.card) {z : ℝ} (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ))
    (k : ℕ) (hmean : hardCoreMean G S z=k) : 21≤k := by
  rcases rank_checked with ⟨hx,hxa,hg,hfactor,hr,hrank⟩
  have hd := ActivityPointDensity.Certificate.transferred_density
    (ActivityPointDensity.Certificate.check_sound ActivityPointDensityData.Point012.checked)
    G hG S (by omega) (a:=(activityLower:ℝ)) (gamma:=(transferFactor:ℝ))
    (by exact_mod_cast hx) (by exact_mod_cast hxa) (activity_lower hz hq)
    (by exact_mod_cast hg) (by exact_mod_cast hfactor)
  have hnR : (80:ℝ)≤S.card := by exact_mod_cast hn
  have hrR : (0:ℝ)≤ActivityPointDensityData.Point012.certificate.parameters.r := by exact_mod_cast hr
  have hgR : (0:ℝ)≤transferFactor := by exact_mod_cast hg
  have hmono := mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left hnR hrR) (ActivityPointDensityData.Point012.certificate.parameters.h:ℝ)) hgR
  have hthreshold : (20:ℝ)<(transferFactor:ℝ)*
      ((ActivityPointDensityData.Point012.certificate.parameters.r:ℝ)*80+ActivityPointDensityData.Point012.certificate.parameters.h) := by
    exact_mod_cast hrank
  rw [hmean] at hd
  by_contra hk
  have hupper : (k:ℝ)≤20 := by exact_mod_cast (show k≤20 by omega)
  linarith

#print axioms activity_lower
#print axioms rank_checked
#print axioms rank_lower
end ForestUnimodality.BridgeRankDensityData.Stage80Cell023
