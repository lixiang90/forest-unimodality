import ForestUnimodality.JointDirectionActual
import ForestUnimodality.Stage350SourceAllOrders
import ForestUnimodality.Stage350AffineTailAllOrders
import ForestUnimodality.Stage900DirectionInputs

namespace ForestUnimodality.Stage350JointInputs
open Real Set JointDirectionBudget JointDirectionActual ReciprocalGradientBudget

noncomputable def ratio (reverse:Bool) (z:ℝ) : ℝ := if reverse then z else 1/z

structure ScalarValid (i:Fin 43) (p:Parameters) (t rmax:ℝ) (reverse:Bool) (P:ℕ→GradientProfile) : Prop where
  start_match : p.start=((Stage350SourceTable.row i).start:ℝ)
  D_match : p.D=((Stage350SourceTable.row i).D:ℝ)
  R_match : p.R=((Stage350SourceTable.row i).R:ℝ)
  vmin_left : p.v≤((Stage350SourceTable.row i).qa:ℝ)*(1-((Stage350SourceTable.row i).qa:ℝ))
  vmin_right : p.v≤((Stage350SourceTable.row i).qb:ℝ)*(1-((Stage350SourceTable.row i).qb:ℝ))
  vmax_left : ((Stage350SourceTable.row i).qb:ℝ)≤1/2 → ((Stage350SourceTable.row i).qb:ℝ)*(1-((Stage350SourceTable.row i).qb:ℝ))≤p.V
  vmax_right : 1/2≤((Stage350SourceTable.row i).qa:ℝ) → ((Stage350SourceTable.row i).qa:ℝ)*(1-((Stage350SourceTable.row i).qa:ℝ))≤p.V
  vmax_center : ((Stage350SourceTable.row i).qa:ℝ)<1/2 → 1/2<((Stage350SourceTable.row i).qb:ℝ) → 1/4≤p.V
  eta_left : |1-2*((Stage350SourceTable.row i).qa:ℝ)|≤p.eta
  eta_right : |1-2*((Stage350SourceTable.row i).qb:ℝ)|≤p.eta
  vmin_near : 9/40≤p.v
  ratio_lt : rmax<1
  ratio_upper : (if reverse then ((Stage350SourceTable.row i).b:ℝ) else 1/((Stage350SourceTable.row i).a:ℝ))≤rmax
  amplifier : rmax/(1-rmax)≤p.amp
  amplifier_squared : rmax≤p.lfactor*(1-rmax)^2
  theta_nonneg : 0≤t
  theta_scale : p.amp^2≤t^2*p.v*p.start
  gradient : ∀j<23,Stage900DirectionInputs.ProfileRange (P j)
    ((Stage350SourceTable.row i).qa:ℝ) ((Stage350SourceTable.row i).qb:ℝ) p.v (JointDirectionSmallCost.cuts p.start j)
  gradient_constant : ∀j<23,(P j).constant=p.smallCoefficient j*(((j:ℝ)+1)/54)

theorem amplification_bounds {p:Parameters} (hp:Valid p) {r rmax:ℝ}
    (hr:0<r) (hrr:r≤rmax) (hmax:rmax<1)
    (ha:rmax/(1-rmax)≤p.amp) (hL:rmax≤p.lfactor*(1-rmax)^2) :
    r/(1-r)≤p.amp ∧ r≤p.lfactor*(1-r)^2 := by
  have hr1:=hrr.trans_lt hmax
  constructor
  · apply le_trans _ ha
    exact div_le_div₀ (hr.le.trans hrr) hrr (sub_pos.mpr hmax) (by linarith)
  · apply hrr.trans (hL.trans _)
    apply mul_le_mul_of_nonneg_left _ hp.2.2.2.2.2.2.2.1
    exact pow_le_pow_left₀ (sub_nonneg.mpr hmax.le) (by linarith) 2

theorem theta_bound {p:Parameters} (hp:Valid p) {r t v m:ℝ}
    (hr:0<r) (hr1:r<1) (ham:r/(1-r)≤p.amp)
    (hm:p.start≤m) (hv:p.v≤v) (ht:0≤t) (hscale:p.amp^2≤t^2*p.v*p.start)
    (reverse:Bool) :
    |-r*JointDirectionGraph.orientation reverse*(1/sqrt (v*m))/(1-r)|≤t := by
  have hm0:=hp.1.trans_le hm
  have hv0:=hp.2.1.trans_le hv
  have hs:0<sqrt (v*m):=sqrt_pos.mpr (mul_pos hv0 hm0)
  have hvm : p.v*p.start≤v*m := mul_le_mul hv hm hp.1.le hv0.le
  have htvm:=mul_le_mul_of_nonneg_left hvm (sq_nonneg t)
  have htpos:0≤t*sqrt (v*m):=mul_nonneg ht hs.le
  have htmp : p.amp≤t*sqrt (v*m) := by nlinarith [sq_sqrt (mul_pos hv0 hm0).le]
  have hdiv : (r/(1-r))/sqrt (v*m)≤t := (div_le_iff₀ hs).mpr (ham.trans htmp)
  have he : |-r*JointDirectionGraph.orientation reverse*(1/sqrt (v*m))/(1-r)|=(r/(1-r))/sqrt (v*m) := by
    cases reverse <;> simp [JointDirectionGraph.orientation,abs_of_pos hr,abs_of_pos (sub_pos.mpr hr1),abs_of_pos hs,abs_mul,abs_div] <;> ring
  rwa [he]

variable {V:Type*} [DecidableEq V]
theorem actual_inputs_of_start (i:Fin 43) (p:Parameters) (hp:Valid p) (t rmax:ℝ)
    (reverse:Bool) (P:ℕ→GradientProfile) (hc:ScalarValid i p t rmax reverse P)
    {G:SimpleGraph V} {S B:Finset V} {z:ℝ} (k:ℕ)
    (hB:IsMaximumMarginalIndependentOn G S B z) (hG:G.IsAcyclic) (hn:0<S.card)
    (hs:p.start≤hardCoreAvailableMean G S B z)
    (hlo:((Stage350SourceTable.row i).a:ℝ)≤z) (hhi:z≤((Stage350SourceTable.row i).b:ℝ))
    (hrank:(S.card:ℝ)/4≤hardCoreMean G S z) (hmean:hardCoreMean G S z=k)
    (hprofile:∀j<40,hardCoreAvailableLowerTail G S B z
      (SignedGaussian350JointData.AlphaFourNinthBeta65.cuts (j+1)*hardCoreAvailableMean G S B z)≤
        exp (-p.profileRate j*hardCoreAvailableMean G S B z))
    (hsmall:∀j<24,hardCoreAvailableLowerTail G S B z
      (JointDirectionSmallCost.cuts (hardCoreAvailableMean G S B z) j)≤
        exp (-p.smallRate j*hardCoreAvailableMean G S B z)) :
    Inputs p G S B z (hardCoreAvailableMean G S B z) (ratio reverse z) t k reverse P := by
  have hrow:=Stage350SourceTable.valid i
  have ha : (0:ℝ)<(Stage350SourceTable.row i).a := by exact_mod_cast hrow.a_pos
  have hz:=ha.trans_le hlo
  have hb:=Stage350SourceAllOrders.actual_bounds_any_size i 1 (by norm_num) hB hG (by omega) hlo hhi hrank
  have hqa : ((Stage350SourceTable.row i).qa:ℝ)=((Stage350SourceTable.row i).a:ℝ)/(1+((Stage350SourceTable.row i).a:ℝ)) := by exact_mod_cast hrow.qa_eq
  have hqb : ((Stage350SourceTable.row i).qb:ℝ)=((Stage350SourceTable.row i).b:ℝ)/(1+((Stage350SourceTable.row i).b:ℝ)) := by exact_mod_cast hrow.qb_eq
  have hqlo : ((Stage350SourceTable.row i).qa:ℝ)≤z/(1+z) := by rw [hqa];exact Stage900SourceTable.activity_fraction_mono ha hlo
  have hqhi : z/(1+z)≤((Stage350SourceTable.row i).qb:ℝ) := by rw [hqb];exact Stage900SourceTable.activity_fraction_mono hz hhi
  have hvmin := (le_min hc.vmin_left hc.vmin_right).trans (bernoulli_variance_ge_min hqlo hqhi)
  have hvmax:=SmoothingInterval.variance_le_interval_max hqlo hqhi hc.vmax_left hc.vmax_right hc.vmax_center
  have hr : 0<ratio reverse z := by cases reverse <;> simp [ratio,hz]
  have hrr : ratio reverse z≤rmax := by
    cases reverse
    · exact (one_div_le_one_div_of_le ha hlo).trans hc.ratio_upper
    · exact hhi.trans hc.ratio_upper
  have hr1:=hrr.trans_lt hc.ratio_lt
  have hamp:=amplification_bounds hp hr hrr hc.ratio_lt hc.amplifier hc.amplifier_squared
  have hk:1≤k := by
    have hnR:(0:ℝ)<S.card:=by exact_mod_cast hn
    rw [hmean] at hrank
    have hkp:(0:ℝ)<k:=by linarith
    have hkN:0<k:=by exact_mod_cast hkp
    omega
  refine ⟨hB.subset,hB.independent,hz,rfl,hs,hmean,hk,?_,?_,hvmin,hvmax,
    hc.vmin_near.trans hvmin,?_,hr,hr1,hamp.1,hamp.2,?_,hprofile,hsmall,?_,hc.gradient_constant⟩
  · have he:=hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz
    rw [hc.R_match]
    nlinarith only [he,hb.centered_variance]
  · rw [hc.D_match]
    exact hb.available_variance
  · exact SmoothingInterval.asymmetry_le_endpoints hqlo hqhi hc.eta_left hc.eta_right
  · exact theta_bound hp hr hr1 hamp.1 hs hvmin hc.theta_nonneg hc.theta_scale reverse
  · intro j hj
    apply Stage900DirectionInputs.profile_valid_of_range (hc.gradient j hj) hp.2.1 hvmin
      (by unfold JointDirectionSmallCost.cuts;have hs0:=hp.1;positivity) ?_ hqlo hqhi
    unfold JointDirectionSmallCost.cuts
    exact mul_le_mul_of_nonneg_left hs (by positivity)

#print axioms amplification_bounds
#print axioms theta_bound
#print axioms actual_inputs_of_start
end ForestUnimodality.Stage350JointInputs
