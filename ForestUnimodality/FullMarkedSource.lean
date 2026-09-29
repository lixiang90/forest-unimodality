import ForestUnimodality.SourceMixtureCertificate

/-! Full-mark source soundness for the stage99 heterogeneous flow. The
(1,1) scalar state controls all vertices, including roots; it does not use
independence of the all-vertex marked set. -/
namespace ForestUnimodality
open Finset

def FullSourceRowValid (P : SourceRowParameters) (lower b : ℝ) : Prop :=
  ∀ p r z : ℝ, 0<p → p≤b/(1+b) → 1/(1+b*(1-p))≤r → r≤1 →
    (p=b/(1+b) → z=1) → 0≤sourceScalarRow P lower b 1 1 p r z

variable {V : Type*} [DecidableEq V]

theorem forest_full_count_variance_of_scalar_certificate (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (activity : V→ℝ) {lower b : ℝ}
    (hlower : 0<lower) (hactivity : ∀x∈S, lower≤activity x ∧ activity x≤b)
    (P : SourceRowParameters) (hP : P.Admissible) (hvalid : FullSourceRowValid P lower b) :
    heterogeneousVariance G S activity (fun J=>(J.card:ℝ)) ≤
      (P.A+P.C)*heterogeneousMean G S activity (fun J=>(J.card:ℝ)) := by
  let Q : SourceRowParameters := ⟨P.A,P.C,P.logPrice,P.phiPrice,P.responsePrice,P.blockingPrice,
    (fun _=>P.positivePrice 1),(fun _=>P.negativePrice 1)⟩
  have hQ : Q.Admissible := ⟨hP.1,hP.2.1,hP.2.2.1,
    fun _=>hP.2.2.2.1 1,fun _=>hP.2.2.2.2 1⟩
  have hact : ∀x∈S, 0<activity x ∧ activity x≤b :=
    fun x hx=>⟨hlower.trans_le (hactivity x hx).1,(hactivity x hx).2⟩
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S activity
    (fun _=>1) (fun x hx=>(hact x hx).1.le)
  have hp : ∀x∈S, 0<p x := fun x hx=>hm.probability_pos (fun y hy=>(hact y hy).1) hx
  have hrow : 0≤∑x∈S,p x*sourceScalarRow Q lower b 1
      (sourceParentMark (fun (_:V)=>1) (parent x)) (p x)
      (heterogeneousMarginal G S activity x/p x) (d x) := by
    apply sum_nonneg
    intro x hx
    apply mul_nonneg (hp x hx).le
    have hh := hvalid (p x) _ (d x) (hp x hx) (hm.probability_le_bound hact hx)
      (hm.retention_bounds hact hx).1 (hm.retention_bounds hact hx).2
      (hm.response_at_probability_endpoint hact hx)
    simpa only [sourceScalarRow,Q] using hh
  have hsum := source_scalar_row_sum G S activity (fun _=>1) parent p d Q lower b
    (fun x hx=>(hp x hx).ne')
  have hpos := hm.positive_capacity_budget_scaled hact Q.positivePrice hQ.2.2.2.1
  have hneg := hm.negative_capacity_budget_scaled hact Q.negativePrice hQ.2.2.2.2
  have hphi := hm.phi_budget_scaled hlower hactivity
  have hblock := hm.blocking_capacity_budget_scaled hact
  have hlog := hm.log_mass_nonneg hlower (fun x hx=>(hactivity x hx).1)
  have hresponse : (∑x∈S,p x*d x)-(∑x∈S,heterogeneousMarginal G S activity x*1)=0 := by
    rw [←hmean,heterogeneousMean_marked_eq_sum_marginals]
    exact sub_self _
  rw [hresponse,mul_zero,←hvar] at hsum
  have hlogPrice := mul_nonneg hQ.1 hlog
  have hphiPrice := mul_nonpos_of_nonneg_of_nonpos hQ.2.1 hphi
  have hblockPrice := mul_nonpos_of_nonneg_of_nonpos hQ.2.2.1 hblock
  have hcard : markedSum (fun (_:V)=>1)=(fun J:Finset V=>(J.card:ℝ)) := by
    funext J; simp [markedSum]
  have hmu := heterogeneousMean_marked_eq_sum_marginals G S activity (fun _=>1)
  rw [hcard] at hvar hsum hmu
  simp only [mul_one,Q] at hsum hmu hlogPrice hphiPrice hblockPrice
  rw [←hmu] at hsum
  nlinarith

#print axioms forest_full_count_variance_of_scalar_certificate
end ForestUnimodality
