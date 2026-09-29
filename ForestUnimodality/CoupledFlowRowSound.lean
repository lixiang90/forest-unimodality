import ForestUnimodality.CoupledFlowRow

namespace ForestUnimodality.CoupledFlow
open Set FixedIndependentTilt ExtendedFlowSources
variable {V : Type*} [DecidableEq V]

theorem Row.actual_step {r : Row} {e : Environment} (hc : r.check e=true) (he : e.check=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z m : ℝ}
    (hzlo : (e.a:ℝ)≤z) (hzhi : z≤(e.b:ℝ)) (hm : 0≤m)
    (havailable : hardCoreAvailableMean G S B z=m)
    (hBcard : (B.card:ℝ)≤m*(e.beta:ℝ)) (hScard : (S.card:ℝ)≤m*(e.gamma:ℝ))
    (hCcard : ((S\B).card:ℝ)≤m*(e.beta:ℝ))
    (hstartW : m*(r.lower:ℝ)≤markedMean G S B z r.start)
    (hstartU : totalMean G S B z r.start≤m*(r.totalUpper:ℝ)) :
    (∀t∈Icc (r.start:ℝ) (r.finish:ℝ),totalMean G S B z t≤m*(r.fine:ℝ)) ∧
    totalMean G S B z r.finish≤m*(r.nextUpper:ℝ) ∧
    m*(r.next:ℝ)≤markedMean G S B z r.finish := by
  have hh : r.Accepts e := of_decide_eq_true hc
  have env : e.Accepts := of_decide_eq_true he
  have ha : (0:ℝ)<e.a := by exact_mod_cast env.1
  have hz := ha.trans_le hzlo
  rcases hh with ⟨hgeom,hdom,hcompar,hrefl⟩
  rcases hgeom with ⟨hs,ho,_,_,_,hpre0,hvb0,hvk0,hkap0,hqu⟩
  rcases hdom with ⟨hse,hfe,hpd,hvd,hed,_,hfull,hcomp⟩
  rcases hcompar with ⟨hpc,hec,_,hpre,hen,_⟩
  rcases hrefl with ⟨hco,hq,hmvb,hmvk,hquad,hvc,hfine,hunext⟩
  have hsR : (0:ℝ)≤r.start := by exact_mod_cast hs
  have hoR : (r.start:ℝ)≤r.finish := by exact_mod_cast ho
  have hes := (r.startExp.check_sound hse).2
  have hef := (r.finishExp.check_sound hfe).1
  push_cast at hes hef
  have variance (s : Source) (U : ℚ)
      (hd : s.domainCheck e.a e.b r.startExpHi r.finishExpLo=true)
      (hU : ∀t∈Icc (r.start:ℝ) (r.finish:ℝ),totalMean G S B z t≤m*(U:ℝ)) :=
    s.actual_variance G hG S B hBS hB ha hzlo hzhi hsR
      (s.domain_sound hd ha.le (hz.trans_le hzhi).le hes hef) hBcard (fun _=>hU)
  have hcoarse := e.coarse_bound (coarse:=(r.coarse:ℝ)) he G hG S B hBS hz hzhi hsR hoR hm hBcard hScard hCcard
    hstartU (by exact_mod_cast hco)
  have hlog (t : ℝ) (ht : t∈Icc (r.start:ℝ) (r.finish:ℝ)) : logisticTilt z t≤(r.qu:ℝ) :=
    FlowVarianceSources.logistic_upper hz hzhi ht.1 hes hq
  have hvarB (t : ℝ) (ht : t∈Icc (r.start:ℝ) (r.finish:ℝ)) : markedVariance G S B z t≤m*(r.VB:ℝ) := by
    have hw := markedMean_le_initial_available G S B hBS hB hz (hsR.trans ht.1)
    rw [havailable] at hw
    have hwu : markedMean G S B z t≤m*(r.qu:ℝ) :=
      hw.trans (by nlinarith [mul_le_mul_of_nonneg_left (hlog t ht) hm])
    exact variance_cap G S B hm (variance r.varSource r.coarse hvd hcoarse t ht) hwu hmvb
  have hvarK (t : ℝ) (ht : t∈Icc (r.start:ℝ) (r.finish:ℝ)) :
      FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
        (fun J=>(J.card:ℝ))≤m*(r.VK:ℝ) := by
    exact r.fullSource.actual_bound hfull G hG S B hBS ha hzlo hzhi hsR hm hef
      hBcard hScard hCcard hcoarse hmvk t ht
  have hcomplement (hp : m*(r.preLower:ℝ)≤markedMean G S B z r.finish) :=
    r.complement.actual_bound G hG S B hBS hz (hzhi.trans (by exact_mod_cast hcomp)) hsR hm
      hBcard hScard hCcard hcoarse hp hvc
  have hp := (FlowComparisonCertificate.Certificate.clamped_sound hpc hpre (le_refl _)).1
  have hn := (FlowComparisonCertificate.Certificate.clamped_sound hec hen (le_refl _)).1
  have hfineR : min (min ((r.totalUpper:ℝ)+(r.kappa:ℝ)*(r.finish-r.start)) r.coarse)
      ((r.totalUpper:ℝ)+max 0 ((r.Vc:ℝ)/4-(1-r.qu)*r.preLower)*(r.finish-r.start))≤r.fine := by
    exact_mod_cast (show _ from hfine : min (min (r.totalUpper+r.kappa*(r.finish-r.start)) r.coarse)
      (r.totalUpper+max 0 (r.Vc/4-(1-r.qu)*r.preLower)*(r.finish-r.start))≤r.fine)
  have hnextR : min (r.fine:ℝ) ((r.totalUpper:ℝ)+
      ((r.Vc:ℝ)/4-(1-r.qu)*r.preLower)*(r.finish-r.start))≤r.nextUpper := by
    exact_mod_cast (show _ from hunext : min r.fine
      (r.totalUpper+(r.Vc/4-(1-r.qu)*r.preLower)*(r.finish-r.start))≤r.nextUpper)
  exact coupled_step (VB:=(r.VB:ℝ)) (VK:=(r.VK:ℝ)) (eta:=(r.kappa:ℝ))
    (Lpre:=(r.preLower:ℝ)) G S B hBS hB hz hoR hm hstartW hstartU hcoarse
    r.preliminary.C_nonneg (by exact_mod_cast hpre0) (variance r.preliminary r.coarse hpd hcoarse)
    (by simpa only [Rat.cast_sub,Row.DP,Row.CP] using hp)
    (by exact_mod_cast hvb0) (by exact_mod_cast hvk0) (by exact_mod_cast hkap0)
    (by exact_mod_cast hquad) hvarB hvarK (by exact_mod_cast hqu) hlog hcomplement
    hfineR hnextR r.endpoint.C_nonneg (variance r.endpoint r.fine hed)
    (by simpa only [Rat.cast_sub,Row.DE,Row.CE] using hn)

theorem Row.variance_bounds {r : Row} {e : Environment} (hc : r.check e=true) (he : e.check=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z m t : ℝ}
    (hzlo : (e.a:ℝ)≤z) (hzhi : z≤(e.b:ℝ)) (hcard : (B.card:ℝ)≤m*(e.beta:ℝ))
    (hFine : ∀u∈Icc (r.start:ℝ) (r.finish:ℝ),totalMean G S B z u≤m*(r.fine:ℝ))
    (ht : t∈Icc (r.start:ℝ) (r.finish:ℝ)) :
    (markedVariance G S B z t≤m*(r.DE e:ℝ)+(r.CE:ℝ)*markedMean G S B z t) ∧
    (markedVariance G S B z t≤m*(r.DI e:ℝ)+(r.CI:ℝ)*markedMean G S B z t) := by
  have hh : r.Accepts e := of_decide_eq_true hc
  have env : e.Accepts := of_decide_eq_true he
  have ha : (0:ℝ)<e.a := by exact_mod_cast env.1
  rcases hh.2.1 with ⟨hse,hfe,_,_,hed,hid,_,_⟩
  have hes := (r.startExp.check_sound hse).2
  have hef := (r.finishExp.check_sound hfe).1
  push_cast at hes hef
  have variance (s : Source) (hd : s.domainCheck e.a e.b r.startExpHi r.finishExpLo=true) :=
    s.actual_variance G hG S B hBS hB ha hzlo hzhi (by exact_mod_cast hh.1.1)
      (s.domain_sound hd ha.le ((ha.trans_le hzlo).trans_le hzhi).le hes hef) hcard (fun _=>hFine) t ht
  exact ⟨variance r.endpoint hed,variance r.integral hid⟩

#print axioms Row.actual_step
#print axioms Row.variance_bounds
end ForestUnimodality.CoupledFlow
