import ForestUnimodality.BasicFlowRow

/-! A finite checked time chain implies the actual fixed-set Laplace bound.
Rows, their adjacencies, and the terminal retention are separate finite checks. -/
namespace ForestUnimodality.BasicFlow
open Finset Set

theorem check_getD (rows : List Row) (fallback : Row) (b beta : ℚ)
    (hc : rows.all (fun r=>r.check b beta)=true) (i : ℕ) (hi : i<rows.length) :
    (rows.getD i fallback).check b beta=true := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    have hp : r.check b beta=true ∧ rs.all (fun r=>r.check b beta)=true := by
      simpa only [List.all_cons,Bool.and_eq_true] using hc
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hp.1
    | succ i =>
      simpa only [List.getD_cons_succ] using ih hp.2 i (by simpa using hi)

structure Table where
  n : ℕ
  qa : ℚ
  b : ℚ
  beta : ℚ
  retention : ℚ
  rate : ℚ
  time : ℕ→ℚ
  lower : ℕ→ℚ
  row : ℕ→Row
  finishExp : ExpEnclosure.PowerCertificate
  finishExpLo : ℚ
  finishExpHi : ℚ

def Table.totalCharge (T : Table) : ℚ := ∑i∈range T.n,(T.row i).charge

def Table.HeaderAccepts (T : Table) : Prop :=
  T.time 0=0 ∧ T.lower 0≤T.qa ∧ 0≤T.retention ∧
  T.finishExp.check (-T.time T.n) T.finishExpLo T.finishExpHi=true ∧
  T.retention≤T.finishExpLo ∧ T.rate≤T.totalCharge

instance (T : Table) : Decidable T.HeaderAccepts := by unfold Table.HeaderAccepts; infer_instance
def Table.headerCheck (T : Table) : Bool := decide T.HeaderAccepts

def Table.connectionCheck (T : Table) (i : ℕ) : Bool := decide
  ((T.row i).start=T.time i ∧ (T.row i).finish=T.time (i+1) ∧
   (T.row i).lower=T.lower i ∧ (T.row i).next=T.lower (i+1))

variable {V : Type*} [DecidableEq V]

theorem Table.actual_laplace (T : Table) (hheader : T.headerCheck=true)
    (hrows : (List.range T.n).all (fun i=>(T.row i).check T.b T.beta)=true)
    (hedges : (List.range T.n).all T.connectionCheck=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z m : ℝ}
    (hz : 0<z) (hzb : z≤(T.b:ℝ)) (hm : 0≤m)
    (hcard : (B.card:ℝ)≤m*(T.beta:ℝ))
    (hinitial : m*(T.qa:ℝ)≤hardCoreOccupiedMass G S B z) :
    hardCoreLayerLaplace G S B z T.retention≤Real.exp (-m*(T.rate:ℝ)) := by
  have hh : T.HeaderAccepts := of_decide_eq_true hheader
  rcases hh with ⟨ht0,hl0,hr0,hexp,hret,hrate⟩
  have row_checked (i : ℕ) (hi : i<T.n) : (T.row i).check T.b T.beta=true :=
    (List.all_eq_true.mp hrows) i (List.mem_range.mpr hi)
  have edges (i : ℕ) (hi : i<T.n) :
      (T.row i).start=T.time i ∧ (T.row i).finish=T.time (i+1) ∧
      (T.row i).lower=T.lower i ∧ (T.row i).next=T.lower (i+1) :=
    of_decide_eq_true ((List.all_eq_true.mp hedges) i (List.mem_range.mpr hi))
  have scalars (i : ℕ) (hi : i<T.n) := (T.row i).scalar_bounds (row_checked i hi)
  have order (i : ℕ) (hi : i<T.n) : (T.time i:ℝ)≤T.time (i+1) := by
    have hs := (scalars i hi).1
    simpa only [(edges i hi).1,(edges i hi).2.1] using hs
  have sources (i : ℕ) (hi : i<T.n) (t : ℝ)
      (ht : t∈Icc (T.time i:ℝ) (T.time (i+1):ℝ)) :
      (heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤m*((T.row i).DE T.beta:ℝ)+(T.row i).CE*
        heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t))) (fun J=>((J∩B).card:ℝ))) ∧
      (heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤m*((T.row i).DI T.beta:ℝ)+(T.row i).CI*
        heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t))) (fun J=>((J∩B).card:ℝ))) := by
    have hrt : t∈Icc ((T.row i).start:ℝ) ((T.row i).finish:ℝ) := by
      simpa only [(edges i hi).1,(edges i hi).2.1] using ht
    have hv := (T.row i).variance_bounds (row_checked i hi) G hG S B hBS hB hz hzb hcard hrt
    have hins : FixedIndependentTilt.inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
    simpa only [FixedIndependentTilt.markedVariance,FixedIndependentTilt.markedMean,
      FixedIndependentTilt.weight_eq_heterogeneous,hins,
      heterogeneousVariance,heterogeneousMean] using hv
  have hstart : m*(T.lower 0:ℝ)≤hardCoreOccupiedMass G S B z :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hl0 : (T.lower 0:ℝ)≤T.qa) hm).trans hinitial
  have hend (i : ℕ) (hi : i<T.n) :
      (T.lower (i+1):ℝ)≤max 0 (PiecewiseFlowZeroSlope.endLower (T.lower i)
        ((T.row i).DE T.beta) (T.row i).CE ((T.time (i+1):ℝ)-T.time i)) := by
    have hs := (scalars i hi).2.2.2.1
    simpa only [(edges i hi).1,(edges i hi).2.1,(edges i hi).2.2.1,
      (edges i hi).2.2.2,Rat.cast_sub] using hs
  have hcharge (i : ℕ) (hi : i<T.n) :
      ((T.row i).charge:ℝ)≤max 0 (PiecewiseFlowZeroSlope.integralLower (T.lower i)
        ((T.row i).DI T.beta) (T.row i).CI ((T.time (i+1):ℝ)-T.time i)) := by
    have hs := (scalars i hi).2.2.2.2
    simpa only [(edges i hi).1,(edges i hi).2.1,(edges i hi).2.2.1,Rat.cast_sub] using hs
  have htime : (T.retention:ℝ)≤Real.exp (-(T.time T.n:ℝ)) := by
    have he := (T.finishExp.check_sound hexp).1
    push_cast at he
    exact (by exact_mod_cast hret : (T.retention:ℝ)≤T.finishExpLo).trans he
  have hl := PiecewiseFlowZeroSlope.actual_laplace_chain_scaled_clamped G S B hBS hB hz hm
    (fun i=>(T.time i:ℝ)) (fun i=>(T.lower i:ℝ)) (fun i=>((T.row i).charge:ℝ))
    (fun i=>((T.row i).DE T.beta:ℝ)) (fun i=>((T.row i).CE:ℝ))
    (fun i=>((T.row i).DI T.beta:ℝ)) (fun i=>((T.row i).CI:ℝ)) T.n
    (by simp only [ht0,Rat.cast_zero]) hstart order
    (fun i hi=>(scalars i hi).2.1) (fun i hi=>(scalars i hi).2.2.1)
    (fun i hi t ht=>(sources i hi t ht).1) (fun i hi t ht=>(sources i hi t ht).2)
    hend hcharge (by exact_mod_cast hr0) htime
  apply hl.trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hm)
  have hr : (T.rate:ℝ)≤T.totalCharge := by exact_mod_cast hrate
  simpa only [Table.totalCharge,Rat.cast_sum] using hr

#print axioms Table.actual_laplace
#print axioms check_getD
end ForestUnimodality.BasicFlow
