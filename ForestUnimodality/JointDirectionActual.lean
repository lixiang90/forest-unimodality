import ForestUnimodality.JointDirectionProfileGraph
import ForestUnimodality.JointDirectionSmallCost

/-! A complete joint directional inequality on an actual finite graph.
There is no size hypothesis: all statistical inputs concern the same law. -/
namespace ForestUnimodality.JointDirectionActual
open Real Set JointDirectionBudget JointDirectionGraph GaussianDirectionFiniteStep
open ReciprocalGradientBudget

structure Envelope (p:Parameters) (t:ℝ) : Prop where
  valid : GaussianDirectionalFamily.HasEnvelope t p.A p.B
  A_pos : 0<p.A
  B_lower : 9/20≤p.B
  t_nonneg : 0≤t
  price_eq : p.price=GaussianDirectionalFamily.badPrice t p.A p.B

variable {V:Type*} [DecidableEq V]
structure Inputs (p:Parameters) (G:SimpleGraph V) (S I:Finset V)
    (z m r t:ℝ) (k:ℕ) (reverse:Bool) (P:ℕ→GradientProfile) : Prop where
  subset : I⊆S
  independent : G.IsIndepSet (I:Set V)
  activity_pos : 0<z
  mean_available : m=hardCoreAvailableMean G S I z
  start_le : p.start≤m
  mean_rank : hardCoreMean G S z=k
  rank_pos : 1≤k
  variance_layer : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤
    p.R*(((z/(1+z))*(1-z/(1+z)))*m)
  variance_available : hardCoreAvailableVariance G S I z≤p.D*m
  variance_min : p.v≤(z/(1+z))*(1-z/(1+z))
  variance_max : (z/(1+z))*(1-z/(1+z))≤p.V
  variance_near : 9/40≤(z/(1+z))*(1-z/(1+z))
  asymmetry : |1-2*(z/(1+z))|≤p.eta
  ratio_pos : 0<r
  ratio_lt : r<1
  amplification : r/(1-r)≤p.amp
  amplification_squared : r≤p.lfactor*(1-r)^2
  theta_bound : |-r*orientation reverse*(1/sqrt (((z/(1+z))*(1-z/(1+z)))*m))/(1-r)|≤t
  profile_tail : ∀i<40,hardCoreAvailableLowerTail G S I z
    (SignedGaussian350JointData.AlphaFourNinthBeta65.cuts (i+1)*m)≤exp (-p.profileRate i*m)
  small_tail : ∀i<24,hardCoreAvailableLowerTail G S I z (JointDirectionSmallCost.cuts m i)≤exp (-p.smallRate i*m)
  gradient : ∀i<23,(P i).Valid (z/(1+z)) p.v (JointDirectionSmallCost.cuts m i)
  gradient_constant : ∀i<23,(P i).constant=p.smallCoefficient i*(((i:ℝ)+1)/54)

variable {p:Parameters} {G:SimpleGraph V} {S I:Finset V} {z m r t:ℝ}
  {k:ℕ} {reverse:Bool} {P:ℕ→GradientProfile}

theorem gaussian_lower (hp:Valid p) (he:Envelope p t) (h:Inputs p G S I z m r t k reverse P) :
    main p m-polynomialCost p m-step p m≤
      (retainedProfile G S I z m (4/9) (k:ℝ) ((z/(1+z))*(1-z/(1+z))) (orientation reverse) 0-
        r*retainedProfile G S I z m (4/9) (k:ℝ) ((z/(1+z))*(1-z/(1+z))) (orientation reverse)
          (1/sqrt (((z/(1+z))*(1-z/(1+z)))*m)))/(1-r) := by
  have hm0:=hp.1.trans_le h.start_le
  have hv:0<(z/(1+z))*(1-z/(1+z)):=hp.2.1.trans_le h.variance_min
  have htail:=h.small_tail 23 (by norm_num)
  rw [JointDirectionSmallCost.cuts_end] at htail
  have hmain:=GaussianDirectionalFamily.HasEnvelope.actual_layer_lower he.valid he.A_pos he.B_lower he.t_nonneg G S I h.subset h.independent
    h.activity_pos h.mean_available hm0 h.mean_rank hv h.theta_bound h.variance_layer h.variance_available htail
  rw [←he.price_eq] at hmain
  have hmain' : main p m-polynomialCost p m≤hardCoreLayerExpectation G S I z
      (fun j M=>if (4/9)*m≤(M:ℝ) then GaussianDirectionalEnvelope.kernel
        (ShiftedLayerMoments.ratio m 0 M) (ShiftedLayerMoments.offset z m 0 (k:ℝ)
          ((z/(1+z))*(1-z/(1+z))) j M)
          (-r*orientation reverse*(1/sqrt (((z/(1+z))*(1-z/(1+z)))*m))/(1-r)) else 0) := by
    simpa only [main,polynomialCost,ShiftedLayerMoments.ratio,ShiftedLayerMoments.offset,add_zero] using hmain
  have hc:=JointDirectionProfileGraph.actual_curve p hp G S I h.subset h.independent h.activity_pos
    h.mean_available hm0 h.mean_rank hv h.variance_layer h.variance_available h.profile_tail
  have hsigma : (orientation reverse)^2=1 := by cases reverse <;> norm_num [orientation]
  have hg:=actual_direction_lower_of_curvature G S I hm0 (by norm_num : (0:ℝ)<4/9)
    hsigma (by positivity : 0≤1/sqrt (((z/(1+z))*(1-z/(1+z)))*m)) h.ratio_pos.le h.ratio_lt hc hmain'
  have hs:=JointDirectionScaling.step_lower p hp h.start_le h.variance_min h.ratio_pos.le h.ratio_lt h.amplification
  linarith

theorem actual_lower (hp:Valid p) (he:Envelope p t) (h:Inputs p G S I z m r t k reverse P) :
    normalizer ((z/(1+z))*(1-z/(1+z))) m*(1-r)*margin p m≤
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
        r*tiltedProbability (countIndependent G S) z (partitionFunction G S z) (if reverse then k-1 else k+1) := by
  have hm0:=hp.1.trans_le h.start_le
  have hv:0<(z/(1+z))*(1-z/(1+z)):=hp.2.1.trans_le h.variance_min
  have ham:1<(4/9)*m := hp.2.2.2.2.2.2.2.2.2.2.2.1 |>.trans_le
    (mul_le_mul_of_nonneg_left h.start_le (by norm_num))
  have hb:=JointDirectionSmallCost.actual_bound p hp G S I h.activity_pos.le hm0 P h.gradient_constant h.small_tail
  have hg:=actual_direction_lower G S I h.subset h.independent h.activity_pos h.mean_available hm0
    (by norm_num : (0:ℝ)<4/9) (by norm_num : (4/9:ℝ)<1) ham hp.2.1 h.variance_min h.variance_near
    h.asymmetry h.variance_available h.ratio_pos h.ratio_lt k h.rank_pos reverse
    (JointDirectionSmallCost.cuts m) P 22 (JointDirectionSmallCost.cuts_start hm0)
    (JointDirectionSmallCost.cuts_end m) (fun i _=>JointDirectionSmallCost.cuts_steps hm0.le i)
    (fun i hi=>h.gradient i (by omega)) hb (gaussian_lower hp he h)
  have herr:=JointDirectionScaling.error_bound p hp h.start_le hv h.variance_max h.ratio_pos.le h.ratio_lt h.amplification_squared
  have hbad:=JointDirectionSmallCost.cost_normalized p hp hm0 hv h.variance_max h.ratio_pos.le h.ratio_lt h.amplification
  unfold margin
  nlinarith

theorem actual_positive (hp:Valid p) (he:Envelope p t) (h:Inputs p G S I z m r t k reverse P)
    (hbudget:0<margin p p.start) :
    0<tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
      r*tiltedProbability (countIndependent G S) z (partitionFunction G S z) (if reverse then k-1 else k+1) := by
  have hm0:=hp.1.trans_le h.start_le
  have hv:0<(z/(1+z))*(1-z/(1+z)):=hp.2.1.trans_le h.variance_min
  have hb:=JointDirectionBudget.margin_positive hp hbudget h.start_le
  have hn:0<normalizer ((z/(1+z))*(1-z/(1+z))) m := by unfold normalizer;positivity
  exact (mul_pos (mul_pos hn (sub_pos.mpr h.ratio_lt)) hb).trans_le (actual_lower hp he h)

#print axioms gaussian_lower
#print axioms actual_lower
#print axioms actual_positive
end ForestUnimodality.JointDirectionActual
