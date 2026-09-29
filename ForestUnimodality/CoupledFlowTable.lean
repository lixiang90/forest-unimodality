import ForestUnimodality.CoupledFlowRowSound

namespace ForestUnimodality.CoupledFlow
open Finset Set FixedIndependentTilt

theorem check_getD (rows : List Row) (fallback : Row) (e : Environment)
    (hc : rows.all (fun r=>r.check e)=true) (i : ℕ) (hi : i<rows.length) :
    (rows.getD i fallback).check e=true := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    have hp : r.check e=true ∧ rs.all (fun r=>r.check e)=true := by
      simpa only [List.all_cons,Bool.and_eq_true] using hc
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hp.1
    | succ i => simpa only [List.getD_cons_succ] using ih hp.2 i (by simpa using hi)

structure Table where
  n : ℕ
  environment : Environment
  qa : ℚ
  initialUpper : ℚ
  retention : ℚ
  rate : ℚ
  time : ℕ→ℚ
  lower : ℕ→ℚ
  upper : ℕ→ℚ
  row : ℕ→Row
  finishExp : ExpEnclosure.PowerCertificate
  finishExpLo : ℚ
  finishExpHi : ℚ

def Table.totalCharge (T : Table) : ℚ := ∑i∈range T.n,(T.row i).charge
def Table.HeaderAccepts (T : Table) : Prop :=
  T.environment.check=true ∧ T.time 0=0 ∧ T.lower 0≤T.qa ∧
  T.initialUpper≤T.upper 0 ∧ 0≤T.retention ∧
  T.finishExp.check (-T.time T.n) T.finishExpLo T.finishExpHi=true ∧
  T.retention≤T.finishExpLo ∧ T.rate≤T.totalCharge
instance (T : Table) : Decidable T.HeaderAccepts := by unfold Table.HeaderAccepts; infer_instance
def Table.headerCheck (T : Table) : Bool := decide T.HeaderAccepts
def Table.connectionCheck (T : Table) (i : ℕ) : Bool := decide
  ((T.row i).start=T.time i ∧ (T.row i).finish=T.time (i+1) ∧
   (T.row i).lower=T.lower i ∧ (T.row i).next=T.lower (i+1) ∧
   (T.row i).totalUpper=T.upper i ∧ (T.row i).nextUpper=T.upper (i+1))

variable {V : Type*} [DecidableEq V]

theorem Table.actual_laplace (T : Table) (hheader : T.headerCheck=true)
    (hrows : (List.range T.n).all (fun i=>(T.row i).check T.environment)=true)
    (hedges : (List.range T.n).all T.connectionCheck=true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z m : ℝ}
    (hzlo : (T.environment.a:ℝ)≤z) (hzhi : z≤(T.environment.b:ℝ)) (hm : 0≤m)
    (havailable : hardCoreAvailableMean G S B z=m)
    (hBcard : (B.card:ℝ)≤m*(T.environment.beta:ℝ))
    (hScard : (S.card:ℝ)≤m*(T.environment.gamma:ℝ))
    (hCcard : ((S\B).card:ℝ)≤m*(T.environment.beta:ℝ))
    (hinitial : m*(T.qa:ℝ)≤hardCoreOccupiedMass G S B z)
    (hmuinitial : totalMean G S B z 0≤m*(T.initialUpper:ℝ)) :
    hardCoreLayerLaplace G S B z T.retention≤Real.exp (-m*(T.rate:ℝ)) := by
  have hh : T.HeaderAccepts := of_decide_eq_true hheader
  rcases hh with ⟨henv,ht0,hl0,hu0,hr0,hexp,hret,hrate⟩
  have env : T.environment.Accepts := of_decide_eq_true henv
  have hz : 0<z := (by exact_mod_cast env.1 : (0:ℝ)<T.environment.a).trans_le hzlo
  have row_checked (i : ℕ) (hi : i<T.n) : (T.row i).check T.environment=true :=
    (List.all_eq_true.mp hrows) i (List.mem_range.mpr hi)
  have edges (i : ℕ) (hi : i<T.n) :
      (T.row i).start=T.time i ∧ (T.row i).finish=T.time (i+1) ∧
      (T.row i).lower=T.lower i ∧ (T.row i).next=T.lower (i+1) ∧
      (T.row i).totalUpper=T.upper i ∧ (T.row i).nextUpper=T.upper (i+1) :=
    of_decide_eq_true ((List.all_eq_true.mp hedges) i (List.mem_range.mpr hi))
  have scalars (i : ℕ) (hi : i<T.n) := (T.row i).scalar_bounds (row_checked i hi)
  have order (i : ℕ) (hi : i<T.n) : (T.time i:ℝ)≤T.time (i+1) := by
    simpa only [(edges i hi).1,(edges i hi).2.1] using (scalars i hi).1
  have hstart : m*(T.lower 0:ℝ)≤hardCoreOccupiedMass G S B z :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hl0 : (T.lower 0:ℝ)≤T.qa) hm).trans hinitial
  have states (i : ℕ) (hi : i≤T.n) :
      m*(T.lower i:ℝ)≤markedMean G S B z (T.time i) ∧
      totalMean G S B z (T.time i)≤m*(T.upper i:ℝ) := by
    induction i with
    | zero =>
      rw [ht0,Rat.cast_zero,markedMean_zero]
      exact ⟨hstart,hmuinitial.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu0) hm)⟩
    | succ i ih =>
      have hi' : i<T.n := by omega
      have hs := ih (by omega)
      have hw : m*((T.row i).lower:ℝ)≤markedMean G S B z (T.row i).start := by
        simpa only [(edges i hi').1,(edges i hi').2.2.1] using hs.1
      have hu : totalMean G S B z (T.row i).start≤m*((T.row i).totalUpper:ℝ) := by
        simpa only [(edges i hi').1,(edges i hi').2.2.2.2.1] using hs.2
      have step := (T.row i).actual_step (row_checked i hi') henv G hG S B hBS hB
        hzlo hzhi hm havailable hBcard hScard hCcard hw hu
      constructor
      · simpa only [(edges i hi').2.1,(edges i hi').2.2.2.1] using step.2.2
      · simpa only [(edges i hi').2.1,(edges i hi').2.2.2.2.2] using step.2.1
  have fine (i : ℕ) (hi : i<T.n) :
      ∀t∈Icc ((T.row i).start:ℝ) ((T.row i).finish:ℝ),totalMean G S B z t≤m*((T.row i).fine:ℝ) := by
    have hs := states i hi.le
    have hw : m*((T.row i).lower:ℝ)≤markedMean G S B z (T.row i).start := by
      simpa only [(edges i hi).1,(edges i hi).2.2.1] using hs.1
    have hu : totalMean G S B z (T.row i).start≤m*((T.row i).totalUpper:ℝ) := by
      simpa only [(edges i hi).1,(edges i hi).2.2.2.2.1] using hs.2
    exact ((T.row i).actual_step (row_checked i hi) henv G hG S B hBS hB
      hzlo hzhi hm havailable hBcard hScard hCcard hw hu).1
  have sources (i : ℕ) (hi : i<T.n) (t : ℝ)
      (ht : t∈Icc (T.time i:ℝ) (T.time (i+1):ℝ)) :
      (heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤m*((T.row i).DE T.environment:ℝ)+(T.row i).CE*
        heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t))) (fun J=>((J∩B).card:ℝ))) ∧
      (heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J=>((J∩B).card:ℝ))≤m*((T.row i).DI T.environment:ℝ)+(T.row i).CI*
        heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t))) (fun J=>((J∩B).card:ℝ))) := by
    have hrt : t∈Icc ((T.row i).start:ℝ) ((T.row i).finish:ℝ) := by
      simpa only [(edges i hi).1,(edges i hi).2.1] using ht
    have hv := (T.row i).variance_bounds (row_checked i hi) henv G hG S B hBS hB hzlo hzhi hBcard (fine i hi) hrt
    have hins : inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
    simpa only [markedVariance,markedMean,weight_eq_heterogeneous,hins,
      heterogeneousVariance,heterogeneousMean] using hv
  have hend (i : ℕ) (hi : i<T.n) :
      (T.lower (i+1):ℝ)≤max 0 (PiecewiseFlowZeroSlope.endLower (T.lower i)
        ((T.row i).DE T.environment) (T.row i).CE ((T.time (i+1):ℝ)-T.time i)) := by
    simpa only [(edges i hi).1,(edges i hi).2.1,(edges i hi).2.2.1,
      (edges i hi).2.2.2.1,Rat.cast_sub] using (scalars i hi).2.2.2.1
  have hcharge (i : ℕ) (hi : i<T.n) :
      ((T.row i).charge:ℝ)≤max 0 (PiecewiseFlowZeroSlope.integralLower (T.lower i)
        ((T.row i).DI T.environment) (T.row i).CI ((T.time (i+1):ℝ)-T.time i)) := by
    simpa only [(edges i hi).1,(edges i hi).2.1,(edges i hi).2.2.1,Rat.cast_sub]
      using (scalars i hi).2.2.2.2
  have htime : (T.retention:ℝ)≤Real.exp (-(T.time T.n:ℝ)) := by
    have he := (T.finishExp.check_sound hexp).1
    push_cast at he
    exact (by exact_mod_cast hret : (T.retention:ℝ)≤T.finishExpLo).trans he
  have hl := PiecewiseFlowZeroSlope.actual_laplace_chain_scaled_clamped G S B hBS hB hz hm
    (fun i=>(T.time i:ℝ)) (fun i=>(T.lower i:ℝ)) (fun i=>((T.row i).charge:ℝ))
    (fun i=>((T.row i).DE T.environment:ℝ)) (fun i=>((T.row i).CE:ℝ))
    (fun i=>((T.row i).DI T.environment:ℝ)) (fun i=>((T.row i).CI:ℝ)) T.n
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
end ForestUnimodality.CoupledFlow
