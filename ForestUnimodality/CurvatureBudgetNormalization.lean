import ForestUnimodality.CurvatureBudget
import ForestUnimodality.CurvatureErrorLayerBudget

/-! Exact square-root normalization; no numerical approximation of real powers. -/
namespace ForestUnimodality.CurvatureBudget
open PointMassSqrtNormalization PointMassBudgetMonotonicity PointMassErrorEnvelope UnboundedBudget

theorem rpow_seven_halves {x : ℝ} (hx : 0<x) : x^(7/2:ℝ)=x^3*Real.sqrt x := by
  rw [show (7/2:ℝ)=(3:ℕ)+(1/2:ℝ) by norm_num,
    Real.rpow_add hx,Real.rpow_natCast,←Real.sqrt_eq_rpow]

theorem coefficient_two : NegativePowerHermite.coefficient 2 (1/3)=15 := by
  unfold NegativePowerHermite.coefficient
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤1/3),Real.rpow_two]
  norm_num

theorem coefficient_five_halves :
    NegativePowerHermite.coefficient (5/2) (1/3)=(81*Real.sqrt 3-24)/4 := by
  unfold NegativePowerHermite.coefficient
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤1/3),rpow_five_halves (by norm_num : (0:ℝ)<1/3)]
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
  norm_num
  ring

theorem tail_eq (p : Parameters) {m : ℝ} (hm : 0<m) :
    tail p m=CurvatureErrorLayerBudget.centralTail m p.vmin p.vmax := by
  unfold tail powerExpCost CurvatureErrorLayerBudget.centralTail
  rw [show (-1/2:ℝ)=-(1/2:ℝ) by ring,Real.rpow_neg hm.le,←Real.sqrt_eq_rpow]
  ring

theorem centralError_eq (p : Parameters) {m : ℝ} (hm : 0<m) :
    CurvatureErrorLayerBudget.centralError m p.vmin p.vmax p.eta p.D=
      cubic p m+quartic p m+tail p m := by
  rw [tail_eq p hm]
  rfl

noncomputable def sqrtExpression (p : Parameters) (m : ℝ) : ℝ :=
  Real.exp (-(2/5:ℝ))*(27/25-(11/10)*p.R)-(4813/1000)*p.D/m-
  (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*p.eta*rho (1/3) m^3*
    (1+15*p.D/m)/Real.sqrt (p.vmin*m)-
  ((5/16)*(rho (1/3) m)^3*Real.sqrt (rho (1/3) m)+1/4)*
    (1+((81*Real.sqrt 3-24)/4)*p.D/m)/(p.vmin*m)-
  Real.sqrt (2*Real.pi)*p.vmax*Real.sqrt p.vmax*
    (3*Real.sqrt m/p.vmin+1/(p.vmin^2*Real.sqrt m))*Real.exp (-(3/2)*p.vmin*m)-
  (Real.sqrt (2*Real.pi)*p.vmax*Real.sqrt p.vmax*(m*Real.sqrt m)*Real.exp (-p.rate 0*m)+
    (Real.pi^3/8)*∑i : Fin 15,(1/(cut i.val*Real.sqrt (cut i.val)))*Real.exp (-p.rate i.succ*m))

theorem budget_eq_sqrtExpression (p : Parameters) {m : ℝ} (hm : 3<m) :
    budget p m=sqrtExpression p m := by
  have hm0 : 0<m := by linarith
  have hr:=rho_pos (show 1<(1/3:ℝ)*m by linarith)
  unfold budget cubic quartic bad momentFactor
  rw [coefficient_two,coefficient_five_halves,rpow_seven_halves hr,tail_eq p hm0]
  simp_rw [rpow_neg_three_halves (cut_pos _)]
  unfold powerExpCost
  rw [rpow_three_halves hm0]
  unfold sqrtExpression CurvatureErrorLayerBudget.centralTail
  ring

#print axioms budget_eq_sqrtExpression
#print axioms centralError_eq
end ForestUnimodality.CurvatureBudget
