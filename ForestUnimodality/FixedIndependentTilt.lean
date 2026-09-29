import ForestUnimodality.PiecewiseFlowLaplace
import ForestUnimodality.ForestSourceLeaf
import ForestUnimodality.LogisticTilt

/-! Exact conditional moments for a fixed independent set whose activity is
changed uniformly. The complement retains its original activity throughout. -/
namespace ForestUnimodality.FixedIndependentTilt
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def weight (B : Finset V) (z x : ℝ) (K : Finset V) : ℝ :=
  z^(K\B).card*x^(K∩B).card
noncomputable def outsideWeight (G : SimpleGraph V) (B : Finset V) (z x : ℝ)
    (J : Finset V) : ℝ := z^J.card*(1+x)^(available G B J).card
noncomputable def inside (B K : Finset V) : ℝ := ((K∩B).card:ℝ)
noncomputable def outside (B K : Finset V) : ℝ := ((K\B).card:ℝ)
noncomputable def conditional (G : SimpleGraph V) (B : Finset V) (x : ℝ)
    (J : Finset V) : ℝ := x/(1+x)*((available G B J).card:ℝ)

/-- Actual independent-subset bijection, with arbitrary outside statistics. -/
theorem numerator_split (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z x : ℝ)
    (F : Finset V → ℕ → ℝ) :
    FiniteTilt.numerator (independentSubsets G S) (weight B z x)
      (fun K=>F (K\B) (K∩B).card) =
    ∑J∈independentSubsets G (S\B), z^J.card*
      ∑T∈(available G B J).powerset, x^T.card*F J T.card := by
  unfold FiniteTilt.numerator weight
  rw [sum_independent_split_statistic G S B hBS hB
    (fun J T=>z^J.card*x^T.card*F J T.card)]
  apply sum_congr rfl
  intro J _
  rw [mul_sum]
  apply sum_congr rfl
  intro T _
  ring

theorem total_eq (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z x : ℝ) :
    FiniteTilt.total (independentSubsets G S) (weight B z x) =
      FiniteTilt.total (independentSubsets G (S\B)) (outsideWeight G B z x) := by
  have hh := numerator_split G S B hBS hB z x (fun _ _=>1)
  simp only [FiniteTilt.numerator,mul_one] at hh
  rw [FiniteTilt.total,hh]
  unfold FiniteTilt.total outsideWeight
  apply sum_congr rfl
  intro J _
  rw [sum_powerset_pow_card]

/-- This equality carries all required first and second mixed moments. -/
theorem moment_transfer (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z x : ℝ)
    (d : ℕ) (f : Finset V → ℝ) (moment : Finset V → ℝ)
    (hmoment : ∀A, (∑T∈A.powerset, x^T.card*(T.card:ℝ)^d)=(1+x)^A.card*moment A) :
    FiniteTilt.mean (independentSubsets G S) (weight B z x)
      (fun K=>f (K\B)*(inside B K)^d) =
    FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x)
      (fun J=>f J*moment (available G B J)) := by
  unfold FiniteTilt.mean
  rw [total_eq G S B hBS hB]
  congr 1
  rw [show (fun K=>f (K\B)*inside B K^d)=(fun K=>f (K\B)*((K∩B).card:ℝ)^d) from rfl,
    numerator_split G S B hBS hB z x (fun J n=>f J*(n:ℝ)^d)]
  unfold FiniteTilt.numerator outsideWeight
  apply sum_congr rfl
  intro J _
  have hi : (∑T∈(available G B J).powerset, x^T.card*(f J*(T.card:ℝ)^d)) =
      f J*((1+x)^(available G B J).card*moment (available G B J)) := by
    rw [←hmoment]
    simp only [mul_sum]
    apply sum_congr rfl
    intro T _
    ring
  rw [hi]
  ring

theorem moment_zero (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z x : ℝ) (f : Finset V → ℝ) :
    FiniteTilt.mean (independentSubsets G S) (weight B z x) (fun K=>f (K\B)) =
    FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x) f := by
  simpa only [pow_zero,mul_one] using moment_transfer G S B hBS hB z x 0 f (fun _=>1)
    (fun A=>by simp only [pow_zero,mul_one]; exact sum_powerset_pow_card A x)

theorem moment_one (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z : ℝ) {x : ℝ} (hx : 0<x)
    (f : Finset V → ℝ) :
    FiniteTilt.mean (independentSubsets G S) (weight B z x)
      (fun K=>f (K\B)*inside B K) =
    FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x)
      (fun J=>f J*conditional G B x J) := by
  simpa only [pow_one,conditional] using
    moment_transfer G S B hBS hB z x 1 f (fun A=>x/(1+x)*(A.card:ℝ))
      (fun A=>by simpa only [pow_one,mul_comm (x^_) (_:ℝ)] using sum_powerset_card_mul_pow A hx)

theorem moment_two (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z : ℝ) {x : ℝ} (hx : 0<x) :
    FiniteTilt.mean (independentSubsets G S) (weight B z x) (fun K=>inside B K^2) =
    FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x)
      (fun J=>conditional G B x J^2+(1-x/(1+x))*conditional G B x J) := by
  have hh := moment_transfer G S B hBS hB z x 2 (fun _=>1)
    (fun A=>(x/(1+x)*(A.card:ℝ))^2+x/(1+x)*(1-x/(1+x))*(A.card:ℝ))
    (fun A=>by simpa only [mul_comm (x^_) (_:ℝ)] using sum_powerset_card_sq_mul_pow A hx)
  simp only [one_mul] at hh
  rw [hh]
  apply FiniteTilt.mean_congr
  intro J _
  unfold conditional
  ring

/-- Completing the square for the common conditional noise. No independence
of the complement count and the number of available vertices is imposed. -/
theorem covariance_identity (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z : ℝ) {x : ℝ} (hx : 0<x) :
    FiniteTilt.covariance (independentSubsets G S) (weight B z x)
      (fun K=>(K.card:ℝ)) (inside B) =
    (1-x/(1+x))*FiniteTilt.mean (independentSubsets G S) (weight B z x) (inside B) +
      FiniteTilt.variance (independentSubsets G (S\B)) (outsideWeight G B z x)
        (fun J=>conditional G B x J+(J.card:ℝ)/2) -
      FiniteTilt.variance (independentSubsets G S) (weight B z x) (outside B)/4 := by
  let f := FiniteTilt.mean (independentSubsets G S) (weight B z x)
  let g := FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x)
  let Q := conditional G B x
  let Y := fun (J:Finset V)=>(J.card:ℝ)
  have hi : f (inside B)=g Q := by
    simpa only [f,g,Q,one_mul] using moment_one G S B hBS hB z hx (fun _=>1)
  have hy : f (outside B)=g Y := moment_zero G S B hBS hB z x Y
  have hy2 : f (fun K=>outside B K^2)=g (fun J=>Y J^2) :=
    moment_zero G S B hBS hB z x (fun J=>(J.card:ℝ)^2)
  have hiy : f (fun K=>outside B K*inside B K)=g (fun J=>Y J*Q J) :=
    moment_one G S B hBS hB z hx Y
  have hi2 : f (fun K=>inside B K^2)=g (fun J=>Q J^2)+(1-x/(1+x))*g Q := by
    rw [show f (fun K=>inside B K^2)=g (fun J=>Q J^2+(1-x/(1+x))*Q J) from
      moment_two G S B hBS hB z hx]
    exact (FiniteTilt.mean_add _ _ _ _).trans (by rw [FiniteTilt.mean_const_mul])
  have hk : (fun K:Finset V=>(K.card:ℝ))=(fun K=>inside B K+outside B K) := by
    funext K
    have hh := split_card K B
    unfold inside outside
    exact_mod_cast (by simpa only [add_comm] using hh)
  have hkx : (fun K:Finset V=>(inside B K+outside B K)*inside B K)=
      (fun K=>inside B K^2+outside B K*inside B K) := by funext K; ring
  have hq2 : (fun J=>(Q J+Y J/2)^2)=
      (fun J=>Q J^2+Y J*Q J+(1/4:ℝ)*Y J^2) := by funext J; ring
  have hq1 : (fun J=>Q J+Y J/2)=(fun J=>Q J+(1/2:ℝ)*Y J) := by funext J; ring
  unfold FiniteTilt.covariance
  rw [hk,hkx,FiniteTilt.mean_add,FiniteTilt.mean_add]
  change f (fun K=>inside B K^2)+f (fun K=>outside B K*inside B K)-
    (f (inside B)+f (outside B))*f (inside B) = _
  rw [hi2,hiy,hi,hy]
  rw [FiniteTilt.variance_eq_second_sub_mean_sq,FiniteTilt.variance_eq_second_sub_mean_sq]
  change _ = (1-x/(1+x))*f (inside B)+(g (fun J=>(Q J+Y J/2)^2)-g (fun J=>Q J+Y J/2)^2)-
    (f (fun K=>outside B K^2)-f (outside B)^2)/4
  rw [hi,hy2,hy,hq2,hq1]
  simp only [g,FiniteTilt.mean_add,FiniteTilt.mean_const_mul]
  ring

omit [DecidableEq V] in
theorem outsideWeight_nonneg (G : SimpleGraph V) (B : Finset V) {z x : ℝ}
    (hz : 0≤z) (hx : 0≤x) (J : Finset V) : 0≤outsideWeight G B z x J := by
  unfold outsideWeight; positivity

theorem outside_total_pos (G : SimpleGraph V) (S B : Finset V) {z x : ℝ}
    (hz : 0≤z) (hx : 0≤x) :
    0<FiniteTilt.total (independentSubsets G (S\B)) (outsideWeight G B z x) := by
  apply (sum_pos_iff_of_nonneg (fun J _=>outsideWeight_nonneg G B hz hx J)).mpr
  refine ⟨∅,empty_mem_independentSubsets G (S\B),?_⟩
  unfold outsideWeight
  simp only [card_empty,pow_zero,one_mul]
  positivity

theorem finite_variance_nonneg {α : Type*} (s : Finset α) (w X : α → ℝ)
    (hw : ∀i∈s, 0≤w i) (hZ : 0<FiniteTilt.total s w) :
    0≤FiniteTilt.variance s w X := by
  rw [FiniteTilt.variance_centered s w X (ne_of_gt hZ)]
  exact div_nonneg (sum_nonneg (fun i hi=>mul_nonneg (hw i hi) (sq_nonneg _))) hZ.le

theorem covariance_lower (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z x : ℝ} (hz : 0≤z) (hx : 0<x) :
    (1-x/(1+x))*FiniteTilt.mean (independentSubsets G S) (weight B z x) (inside B) -
      FiniteTilt.variance (independentSubsets G S) (weight B z x) (outside B)/4 ≤
    FiniteTilt.covariance (independentSubsets G S) (weight B z x)
      (fun K=>(K.card:ℝ)) (inside B) := by
  rw [covariance_identity G S B hBS hB z hx]
  have hh := finite_variance_nonneg (independentSubsets G (S\B)) (outsideWeight G B z x)
    (fun J=>conditional G B x J+(J.card:ℝ)/2)
    (fun J _=>outsideWeight_nonneg G B hz hx.le J) (outside_total_pos G S B hz hx.le)
  linarith

theorem variance_const_mul {α : Type*} (s : Finset α) (w X : α → ℝ) (c : ℝ) :
    FiniteTilt.variance s w (fun i=>c*X i)=c^2*FiniteTilt.variance s w X := by
  simp only [FiniteTilt.variance_eq_second_sub_mean_sq,mul_pow,FiniteTilt.mean_const_mul]
  ring

theorem marked_variance_identity (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) (z : ℝ) {x : ℝ} (hx : 0<x) :
    FiniteTilt.variance (independentSubsets G S) (weight B z x) (inside B) =
      (1-x/(1+x))*FiniteTilt.mean (independentSubsets G S) (weight B z x) (inside B)+
      (x/(1+x))^2*FiniteTilt.variance (independentSubsets G (S\B)) (outsideWeight G B z x)
        (fun J=>((available G B J).card:ℝ)) := by
  have hm : FiniteTilt.mean (independentSubsets G S) (weight B z x) (inside B)=
      FiniteTilt.mean (independentSubsets G (S\B)) (outsideWeight G B z x) (conditional G B x) := by
    simpa only [one_mul] using moment_one G S B hBS hB z hx (fun _=>1)
  rw [←variance_const_mul,show (fun J=>x/(1+x)*((available G B J).card:ℝ))=conditional G B x from rfl]
  rw [FiniteTilt.variance_eq_second_sub_mean_sq,FiniteTilt.variance_eq_second_sub_mean_sq,
    moment_two G S B hBS hB z hx,FiniteTilt.mean_add,FiniteTilt.mean_const_mul,hm]
  ring

theorem weight_eq_tilt (B : Finset V) (z t : ℝ) :
    weight B z (z*Real.exp (-t)) =
    FiniteTilt.tilt (heterogeneousWeight (fun (_:V)=>z)) (fun K=>-inside B K) t := by
  funext K
  unfold weight FiniteTilt.tilt heterogeneousWeight inside
  rw [prod_const,mul_pow,←mul_assoc,←pow_add,←split_card K B,←Real.exp_nat_mul]
  congr 2
  ring

theorem weight_eq_heterogeneous (B : Finset V) (z t : ℝ) :
    weight B z (z*Real.exp (-t)) =
    heterogeneousWeight (independentTiltActivities B z (Real.exp (-t))) := by
  rw [weight_eq_tilt]
  funext K
  exact (independent_tilt_weight_eq B K z t).symm

noncomputable def markedMean (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) : ℝ :=
  FiniteTilt.mean (independentSubsets G S) (weight B z (z*Real.exp (-t))) (inside B)
noncomputable def totalMean (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) : ℝ :=
  FiniteTilt.mean (independentSubsets G S) (weight B z (z*Real.exp (-t))) (fun K=>(K.card:ℝ))
noncomputable def markedVariance (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) : ℝ :=
  FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t))) (inside B)
noncomputable def complementVariance (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) : ℝ :=
  FiniteTilt.variance (independentSubsets G S) (weight B z (z*Real.exp (-t))) (outside B)
noncomputable def availabilityVariance (G : SimpleGraph V) (S B : Finset V) (z t : ℝ) : ℝ :=
  FiniteTilt.variance (independentSubsets G (S\B)) (outsideWeight G B z (z*Real.exp (-t)))
    (fun J=>((available G B J).card:ℝ))

theorem tilted_total_pos (G : SimpleGraph V) (S B : Finset V) {z : ℝ} (hz : 0<z) (t : ℝ) :
    0<FiniteTilt.total (independentSubsets G S) (weight B z (z*Real.exp (-t))) := by
  rw [weight_eq_heterogeneous]
  apply heterogeneousPartition_pos
  intro v _
  unfold independentTiltActivities
  split_ifs <;> positivity

theorem hasDerivAt_markedMean (G : SimpleGraph V) (S B : Finset V) {z : ℝ} (hz : 0<z) (t : ℝ) :
    HasDerivAt (markedMean G S B z) (-markedVariance G S B z t) t := by
  have hh := FiniteTilt.hasDerivAt_mean (independentSubsets G S)
    (heterogeneousWeight (fun (_:V)=>z)) (fun K=>-inside B K) (inside B) t
    (by rw [←weight_eq_tilt]; exact ne_of_gt (tilted_total_pos G S B hz t))
  unfold markedMean
  simpa only [markedVariance,weight_eq_tilt,FiniteTilt.covariance_neg_right,FiniteTilt.variance] using hh

theorem hasDerivAt_totalMean (G : SimpleGraph V) (S B : Finset V) {z : ℝ} (hz : 0<z) (t : ℝ) :
    HasDerivAt (totalMean G S B z)
      (-FiniteTilt.covariance (independentSubsets G S) (weight B z (z*Real.exp (-t)))
        (fun K=>(K.card:ℝ)) (inside B)) t := by
  have hh := FiniteTilt.hasDerivAt_mean (independentSubsets G S)
    (heterogeneousWeight (fun (_:V)=>z)) (fun K=>-inside B K) (fun K=>(K.card:ℝ)) t
    (by rw [←weight_eq_tilt]; exact ne_of_gt (tilted_total_pos G S B hz t))
  unfold totalMean
  simpa only [weight_eq_tilt,FiniteTilt.covariance_neg_right] using hh

/-- Stage99/80's signed drift, derived from the actual fixed-B law. -/
theorem totalMean_derivative_upper (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z : ℝ} (hz : 0<z) (t : ℝ) :
    deriv (totalMean G S B z) t ≤
      complementVariance G S B z t/4-(1-logisticTilt z t)*markedMean G S B z t := by
  rw [(hasDerivAt_totalMean G S B hz t).deriv]
  have hh := covariance_lower G S B hBS hB hz.le (mul_pos hz (Real.exp_pos (-t)))
  change _ ≤ _ at hh
  dsimp only [complementVariance,markedMean,logisticTilt]
  linarith

theorem hasDerivAt_markedMean_div_logistic (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z : ℝ} (hz : 0<z) (t : ℝ) :
    HasDerivAt (fun u=>markedMean G S B z u/logisticTilt z u)
      (-logisticTilt z t*availabilityVariance G S B z t) t := by
  have hh := (hasDerivAt_markedMean G S B hz t).div (hasDerivAt_logisticTilt hz t)
    (ne_of_gt (logisticTilt_pos hz t))
  apply hh.congr_deriv
  have hi := marked_variance_identity G S B hBS hB z (mul_pos hz (Real.exp_pos (-t)))
  change markedVariance G S B z t=(1-logisticTilt z t)*markedMean G S B z t+
    (logisticTilt z t)^2*availabilityVariance G S B z t at hi
  rw [hi]
  field_simp [ne_of_gt (logisticTilt_pos hz t)]
  ring

theorem markedMean_div_logistic_antitone (G : SimpleGraph V) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z : ℝ} (hz : 0<z) :
    Antitone (fun t=>markedMean G S B z t/logisticTilt z t) := by
  apply antitone_of_deriv_nonpos
    (fun t=>(hasDerivAt_markedMean_div_logistic G S B hBS hB hz t).differentiableAt)
  intro t
  rw [(hasDerivAt_markedMean_div_logistic G S B hBS hB hz t).deriv]
  have hv : 0≤availabilityVariance G S B z t :=
    finite_variance_nonneg _ _ _ (fun J _=>outsideWeight_nonneg G B hz.le (by positivity) J)
      (outside_total_pos G S B hz.le (by positivity))
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (logisticTilt_pos hz t).le) hv

#print axioms weight_eq_tilt
#print axioms totalMean_derivative_upper
#print axioms hasDerivAt_markedMean_div_logistic
#print axioms markedMean_div_logistic_antitone
#print axioms covariance_identity
#print axioms covariance_lower
#print axioms numerator_split
#print axioms total_eq
#print axioms moment_transfer
#print axioms moment_zero
#print axioms moment_one
#print axioms moment_two
end ForestUnimodality.FixedIndependentTilt
