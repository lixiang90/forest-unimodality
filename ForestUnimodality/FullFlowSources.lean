import ForestUnimodality.CoupledFlowSources
import ForestUnimodality.Stage99FullSourceLibrary

namespace ForestUnimodality.CoupledFlow
open Set FixedIndependentTilt

inductive FullSource where
  | uniform : Fin 16→FullSource
  | full : Fin 3→FullSource
  deriving DecidableEq
def FullSource.bound : FullSource→ℚ→ℚ→ℚ
  | .uniform i,gamma,_ => (NonnegativeSourceLibrary.parameters i).A*gamma
  | .full i,_,U => ((Stage99FullSourceLibrary.parameters i).A+(Stage99FullSourceLibrary.parameters i).C)*U
def FullSource.DomainAccepts : FullSource→ℚ→ℚ→ℚ→Prop
  | .uniform i,_,b,_ => b≤(NonnegativeSourceLibrary.parameters i).b
  | .full i,a,b,flo => (Stage99FullSourceLibrary.domain i).lower≤a*flo ∧
      b≤(Stage99FullSourceLibrary.domain i).b
instance (s : FullSource) (a b flo : ℚ) : Decidable (s.DomainAccepts a b flo) := by
  cases s <;> unfold FullSource.DomainAccepts <;> infer_instance
def FullSource.domainCheck (s : FullSource) (a b flo : ℚ) : Bool := decide (s.DomainAccepts a b flo)

variable {V : Type*} [DecidableEq V]
theorem FullSource.actual_bound (s : FullSource) {a b flo beta gamma U v : ℚ}
    (hd : s.domainCheck a b flo=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (hBS : B⊆S)
    {z start finish m : ℝ} (ha : (0:ℝ)<a) (hzlo : (a:ℝ)≤z) (hzhi : z≤(b:ℝ))
    (hs : 0≤start) (hm : 0≤m) (he : (flo:ℝ)≤Real.exp (-finish))
    (hBcard : (B.card:ℝ)≤m*(beta:ℝ)) (hScard : (S.card:ℝ)≤m*(gamma:ℝ))
    (hCcard : ((S\B).card:ℝ)≤m*(beta:ℝ))
    (hU : ∀t∈Icc start finish,totalMean G S B z t≤m*(U:ℝ))
    (hv : s.bound gamma U≤v) :
    ∀t∈Icc start finish,
      FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
        (fun J=>(J.card:ℝ))≤m*(v:ℝ) := by
  have hdom : s.DomainAccepts a b flo := of_decide_eq_true hd
  have hvr : (s.bound gamma U:ℝ)≤v := by exact_mod_cast hv
  cases s with
  | uniform i =>
    intro t ht
    have hh := (uniform_variance_caps i G hG S B hBS (ha.trans_le hzlo)
      (hzhi.trans (by exact_mod_cast hdom)) (hs.trans ht.1) hBcard hScard hCcard).2.1
    exact hh.trans (by simpa only [FullSource.bound,Rat.cast_mul] using mul_le_mul_of_nonneg_left hvr hm)
  | full i =>
    have hlo : ((Stage99FullSourceLibrary.domain i).lower:ℝ)≤(a:ℝ)*Real.exp (-finish) :=
      (by exact_mod_cast hdom.1 : ((Stage99FullSourceLibrary.domain i).lower:ℝ)≤(a:ℝ)*flo).trans
        (mul_le_mul_of_nonneg_left he ha.le)
    have hh := Stage99FullSourceLibrary.variance_on_step i G hG S B ha hzlo hzhi hs hlo
      (by exact_mod_cast hdom.2) hU
    intro t ht
    exact (hh t ht).trans (by
      simpa only [FullSource.bound,Rat.cast_add,Rat.cast_mul] using mul_le_mul_of_nonneg_left hvr hm)

#print axioms FullSource.actual_bound
end ForestUnimodality.CoupledFlow
