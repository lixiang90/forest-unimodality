import ForestUnimodality.JointDirectionBudget
import ForestUnimodality.PointMassSqrtNormalization

/-! Exact square-root central costs and a proved rational-exponent tail
majorant, used only for certification of the joint-direction endpoint. -/
namespace ForestUnimodality.JointDirectionEndpoint
open Real DirectionalMomentMonotonicity PointMassBudgetMonotonicity PointMassErrorEnvelope JointDirectionBudget

theorem moment_coefficients :
    NegativePowerHermite.coefficient 1 (4/9)=9/4 ∧
    NegativePowerHermite.coefficient (3/2) (4/9)=999/200 ∧
    NegativePowerHermite.coefficient 2 (4/9)=153/16 ∧
    NegativePowerHermite.coefficient (5/2) (4/9)=13491/800 := by
  have hs : sqrt (4/9:ℝ)=2/3 := by norm_num
  have h32:=PointMassSqrtNormalization.rpow_neg_three_halves (by norm_num : (0:ℝ)<4/9)
  have h52 : (4/9:ℝ)^(-(5/2:ℝ))=243/32 := by
    rw [rpow_neg (by norm_num : (0:ℝ)≤4/9), PointMassSqrtNormalization.rpow_five_halves (by norm_num),hs]
    norm_num
  norm_num [NegativePowerHermite.coefficient,rpow_neg_one,h32,h52,hs,rpow_neg,rpow_two]

noncomputable def zero (v eta D m : ℝ) : ℝ :=
  eta*rho (4/9) m^2/(3*Real.pi*v*sqrt m)*(1+(9/4)*D/m)+
  (rho (4/9) m^2*sqrt (rho (4/9) m))/(16*sqrt (2*Real.pi)*v*sqrt v*m)*(1+(999/200)*D/m)+
  exp (-2*v*m)/(4*v*sqrt m)

noncomputable def two (v eta D m : ℝ) : ℝ :=
  (4*eta*rho (4/9) m^3)/(3*Real.pi*v^2*sqrt m)*(1+(153/16)*D/m)+
  (5*rho (4/9) m^3*sqrt (rho (4/9) m))/(16*sqrt (2*Real.pi)*v^2*sqrt v*m)*(1+(13491/800)*D/m)+
  ((9*sqrt m)/(4*v)+9/(16*v^2*sqrt m))*exp (-2*v*m)

theorem tail_bound {v m : ℝ} (hv:0<v) (hm:0<m) :
    exp (-decayRate (4/9) v*m)≤exp (-2*v*m) ∧
    1/(Real.pi^2*v*(4/9))≤1/(4*v) ∧
    1/(Real.pi^2*v^2*(4/9)^2)≤9/(16*v^2) := by
  have hp : (9:ℝ)≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
  constructor
  · apply exp_le_exp.mpr
    unfold decayRate
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_pos hv hm).le]
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hv.le]
  · rw [show (9:ℝ)/(16*v^2)=1/(9*v^2*(4/9)^2) by ring]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg v)]

theorem uZero_le {v eta D m : ℝ} (hv:0<v) (hm:0<m) (ham:1<(4/9)*m) :
    uZero (4/9) v eta D m≤zero v eta D m := by
  have hr:=rho_pos ham
  have ht:=tail_bound hv hm
  have htail : 1/(Real.pi^2*v*(4/9))*UnboundedBudget.powerExpCost (-1/2) (decayRate (4/9) v) m≤
      exp (-2*v*m)/(4*v*sqrt m) := by
    unfold UnboundedBudget.powerExpCost
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by norm_num,rpow_neg hm.le,←sqrt_eq_rpow]
    have h:=mul_le_mul ht.2.1 (mul_le_mul_of_nonneg_left ht.1 (inv_nonneg.mpr (sqrt_nonneg m)))
      (by positivity) (by positivity : (0:ℝ)≤1/(4*v))
    convert! h using 1
    all_goals ring_nf
  unfold uZero zero powerMoment momentFactor
  rw [moment_coefficients.1,moment_coefficients.2.1,
    PointMassSqrtNormalization.rpow_five_halves hr,PointMassSqrtNormalization.rpow_three_halves hv,
    rpow_one,←sqrt_eq_rpow,show (2:ℝ)=(2:ℕ) by norm_num,rpow_natCast]
  convert! add_le_add_left htail
    (eta*rho (4/9) m^2/(3*Real.pi*v*sqrt m)*(1+(9/4)*D/m)+
      (rho (4/9) m^2*sqrt (rho (4/9) m))/(16*sqrt (2*Real.pi)*v*sqrt v*m)*(1+(999/200)*D/m)) using 1
  all_goals ring_nf

theorem uTwo_le {v eta D m : ℝ} (hv:0<v) (hm:0<m) (ham:1<(4/9)*m) :
    uTwo (4/9) v eta D m≤two v eta D m := by
  have hr:=rho_pos ham
  have ht:=tail_bound hv hm
  have htail : (1/(v*(4/9)))*UnboundedBudget.powerExpCost (1/2) (decayRate (4/9) v) m+
      (1/(Real.pi^2*v^2*(4/9)^2))*UnboundedBudget.powerExpCost (-1/2) (decayRate (4/9) v) m≤
      ((9*sqrt m)/(4*v)+9/(16*v^2*sqrt m))*exp (-2*v*m) := by
    unfold UnboundedBudget.powerExpCost
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by norm_num,rpow_neg hm.le,←sqrt_eq_rpow]
    have h0:=mul_le_mul_of_nonneg_left ht.1 (show 0≤1/(v*(4/9))*sqrt m by positivity)
    have h1:=mul_le_mul ht.2.2 (mul_le_mul_of_nonneg_left ht.1 (inv_nonneg.mpr (sqrt_nonneg m)))
      (by positivity) (by positivity : (0:ℝ)≤9/(16*v^2))
    convert! add_le_add h0 h1 using 1
    all_goals ring_nf
  unfold uTwo two powerMoment momentFactor
  rw [moment_coefficients.2.2.1,moment_coefficients.2.2.2,
    show (7/2:ℝ)=(3:ℕ)+1/2 by norm_num,DirectionalErrorEnvelope.half_power hr,
    PointMassSqrtNormalization.rpow_five_halves hv,
    rpow_one,←sqrt_eq_rpow,show (3:ℝ)=(3:ℕ) by norm_num,rpow_natCast]
  convert! add_le_add_left htail
    ((4*eta*rho (4/9) m^3)/(3*Real.pi*v^2*sqrt m)*(1+(153/16)*D/m)+
      (5*rho (4/9) m^3*sqrt (rho (4/9) m))/(16*sqrt (2*Real.pi)*v^2*sqrt v*m)*(1+(13491/800)*D/m)) using 1
  all_goals ring_nf

noncomputable def finiteError (p:Parameters) (m:ℝ) : ℝ :=
  sqrt (2*Real.pi*p.V)*sqrt ((zero p.v p.eta p.D m)^2+
    (p.lfactor/m)*zero p.v p.eta p.D m*two p.v p.eta p.D m)
noncomputable def margin (p:Parameters) (m:ℝ) : ℝ :=
  JointDirectionBudget.main p m-JointDirectionBudget.polynomialCost p m-
    finiteError p m-JointDirectionBudget.step p m-JointDirectionBudget.small p m

theorem finiteError_le {p:Parameters} (hp:Valid p) {m:ℝ} (hm:p.start≤m) :
    JointDirectionBudget.finiteError p m≤finiteError p m := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,rest⟩
  have hm0:=hs.trans_le hm
  have ham':=ham.trans_le (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4/9))
  have h0:=uZero_le (eta:=p.eta) (D:=p.D) hv hm0 ham'
  have h2:=uTwo_le (eta:=p.eta) (D:=p.D) hv hm0 ham'
  have hn0:=uZero_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hm0 ham'
  have hn2:=uTwo_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hm0 ham'
  unfold JointDirectionBudget.finiteError finiteError
  apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
  apply sqrt_le_sqrt
  apply add_le_add (pow_le_pow_left₀ hn0 h0 2)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h0 (div_nonneg hlf hm0.le)) h2 hn2
    (mul_nonneg (div_nonneg hlf hm0.le) (hn0.trans h0))

theorem margin_le {p:Parameters} (hp:Valid p) {m:ℝ} (hm:p.start≤m) :
    margin p m≤JointDirectionBudget.margin p m := by
  have h:=finiteError_le hp hm
  unfold margin JointDirectionBudget.margin
  linarith

noncomputable def smallSqrt (p:Parameters) (m:ℝ) : ℝ :=
  p.amp*sqrt (2*Real.pi*p.V)*(sqrt m*exp (-p.smallRate 0*m)+
    (1/(p.v*sqrt m))*(p.smallCoefficient 22*exp (-p.smallRate 23*m)+
      ∑i∈Finset.range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*exp (-p.smallRate (i+1)*m)))

theorem small_eq_sqrt (p:Parameters) {m:ℝ} (hm:0<m) :
    JointDirectionBudget.small p m=smallSqrt p m := by
  unfold JointDirectionBudget.small smallSqrt UnboundedBudget.powerExpCost
  rw [show (-1/2:ℝ)=-(1/2:ℝ) by norm_num,rpow_neg hm.le,←sqrt_eq_rpow]
  rw [show (∑i∈Finset.range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*
      ((sqrt m)⁻¹*exp (-p.smallRate (i+1)*m)))=
      (sqrt m)⁻¹*∑i∈Finset.range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*exp (-p.smallRate (i+1)*m) by
    rw [Finset.mul_sum];apply Finset.sum_congr rfl; intro i hi;ring]
  ring

#print axioms moment_coefficients
#print axioms uZero_le
#print axioms uTwo_le
#print axioms margin_le
end ForestUnimodality.JointDirectionEndpoint
