import ForestUnimodality.FlowSourceDomainCheck
import ForestUnimodality.FlowNormalization
import ForestUnimodality.CoupledFlowStep

namespace ForestUnimodality.CoupledFlow
open Set FixedIndependentTilt FlowVarianceSources

structure Environment where
  a : ℚ
  b : ℚ
  beta : ℚ
  gamma : ℚ
  uniform : Fin 16
  eta : ℚ
  globalCap : ℚ

def Environment.M (e : Environment) : ℚ := (NonnegativeSourceLibrary.parameters e.uniform).A
def Environment.Accepts (e : Environment) : Prop :=
  0<e.a ∧ 0≤e.beta ∧ 0≤e.gamma ∧
  e.b≤(NonnegativeSourceLibrary.parameters e.uniform).b ∧ 0≤e.eta ∧
  (e.M*e.beta)*(e.M*e.gamma)≤e.eta^2 ∧ e.b/(1+e.b)*e.gamma≤e.globalCap
instance (e : Environment) : Decidable e.Accepts := by unfold Environment.Accepts; infer_instance
def Environment.check (e : Environment) : Bool := decide e.Accepts

inductive ComplementSource where
  | uniform : Fin 16→ComplementSource
  | support : Fin 15→ComplementSource
  deriving DecidableEq

def ComplementSource.bound : ComplementSource→ℚ→ℚ→ℚ→ℚ
  | .uniform i,beta,_,_ => (NonnegativeSourceLibrary.parameters i).A*beta
  | .support i,beta,U,L => (AffineSourceLibrary.parameters i).A*beta+
      (AffineSourceLibrary.parameters i).C*max 0 (U-L)
def ComplementSource.cap : ComplementSource→ℚ
  | .uniform i => (NonnegativeSourceLibrary.parameters i).b
  | .support i => (AffineSourceLibrary.domain i).b

variable {V : Type*} [DecidableEq V]

theorem Environment.coarse_bound {e : Environment} (he : e.check=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    {z start finish m U coarse : ℝ}
    (hz : 0<z) (hzb : z≤(e.b:ℝ)) (hs : 0≤start) (ho : start≤finish) (hm : 0≤m)
    (hBcard : (B.card:ℝ)≤m*(e.beta:ℝ)) (hScard : (S.card:ℝ)≤m*(e.gamma:ℝ))
    (hCcard : ((S\B).card:ℝ)≤m*(e.beta:ℝ))
    (hU : totalMean G S B z start≤m*U)
    (hc : min (U+(e.eta:ℝ)*(finish-start)) e.globalCap≤coarse) :
    ∀t∈Icc start finish,totalMean G S B z t≤m*coarse := by
  have hh : e.Accepts := of_decide_eq_true he
  rcases hh with ⟨_,hbeta,hgamma,hcap,heta,hquad,hglobal⟩
  have hzb' : z≤((NonnegativeSourceLibrary.parameters e.uniform).b:ℝ) :=
    hzb.trans (by exact_mod_cast hcap)
  have hv (t : ℝ) (ht : t∈Icc start finish) :=
    uniform_variance_caps e.uniform G hG S B hBS hz hzb' (hs.trans ht.1) hBcard hScard hCcard
  have hM : (0:ℝ)≤e.M :=
    (NonnegativeSource.Parameters.check_sound (NonnegativeSourceLibrary.parameters_checked e.uniform)).A_nonneg
  have hg (t : ℝ) (ht : t∈Icc start finish) : totalMean G S B z t≤m*(e.globalCap:ℝ) := by
    have h := totalMean_global_cap G hG S B hz hzb (hs.trans ht.1) (by simpa [mul_comm] using hScard)
    have hh : (e.b:ℝ)/(1+e.b)*e.gamma≤e.globalCap := by exact_mod_cast hglobal
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hh hm])
  have h := coarse_totalMean_on_step (eta:=(e.eta:ℝ)) G S B hz ho hm
    (mul_nonneg hM (by exact_mod_cast hbeta)) (mul_nonneg hM (by exact_mod_cast hgamma))
    (by exact_mod_cast heta) (by exact_mod_cast hquad) hU
    (fun t ht=>(hv t ht).1) (fun t ht=>(hv t ht).2.1) hg
  intro t ht
  exact (h t ht).trans (mul_le_mul_of_nonneg_left hc hm)

theorem ComplementSource.actual_bound (s : ComplementSource)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    {z start finish m : ℝ} {beta gamma U L v : ℚ}
    (hz : 0<z) (hzb : z≤(s.cap:ℝ)) (hs : 0≤start) (hm : 0≤m)
    (hBcard : (B.card:ℝ)≤m*(beta:ℝ)) (hScard : (S.card:ℝ)≤m*(gamma:ℝ))
    (hCcard : ((S\B).card:ℝ)≤m*(beta:ℝ))
    (hU : ∀t∈Icc start finish,totalMean G S B z t≤m*(U:ℝ))
    (hL : m*(L:ℝ)≤markedMean G S B z finish)
    (hv : s.bound beta U L≤v) :
    ∀t∈Icc start finish,complementVariance G S B z t≤m*(v:ℝ) := by
  have hvr : (s.bound beta U L:ℝ)≤v := by exact_mod_cast hv
  cases s with
  | uniform i =>
    intro t ht
    have hh := (uniform_variance_caps i G hG S B hBS hz hzb (hs.trans ht.1) hBcard hScard hCcard).2.2
    exact hh.trans (by simpa only [ComplementSource.bound,Rat.cast_mul] using mul_le_mul_of_nonneg_left hvr hm)
  | support i =>
    have hp := AffineSource.Parameters.check_sound (AffineSourceLibrary.parameters_checked i)
    have hh := complement_affine_cap G hG S B hz hzb hs hm
      (AffineSourceLibrary.parameters i).toReal hp.1 (AffineSourceLibrary.source_valid i)
      hp.2.1 (AffineSourceLibrary.C_pos i).le hCcard hU hL
    intro t ht
    exact (hh t ht).trans (by
      simpa only [ComplementSource.bound,Rat.cast_add,Rat.cast_mul,Rat.cast_max,Rat.cast_sub,
        Rat.cast_zero,AffineSource.Parameters.toReal] using mul_le_mul_of_nonneg_left hvr hm)

#print axioms Environment.coarse_bound
#print axioms ComplementSource.actual_bound
end ForestUnimodality.CoupledFlow
