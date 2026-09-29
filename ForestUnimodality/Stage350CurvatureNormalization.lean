import ForestUnimodality.Stage350CurvatureBudget

namespace ForestUnimodality.Stage350CurvatureBudget
open Real PointMassSqrtNormalization PointMassBudgetMonotonicity PointMassErrorEnvelope UnboundedBudget

theorem coefficient_two : NegativePowerHermite.coefficient 2 (7/20)=680/49 := by
  unfold NegativePowerHermite.coefficient
  rw [rpow_neg (by norm_num : (0:ℝ)≤7/20),rpow_two]
  norm_num

theorem coefficient_five_halves : NegativePowerHermite.coefficient (5/2) (7/20)=
    (1/((7/20:ℝ)^2*sqrt (7/20))-1+(5/2)*(7/20-1))/(1-7/20)^2 := by
  unfold NegativePowerHermite.coefficient
  rw [rpow_neg (by norm_num : (0:ℝ)≤7/20),rpow_five_halves (by norm_num : (0:ℝ)<7/20)]
  simp only [one_div]

theorem coefficient_seven_halves : NegativePowerHermite.coefficient (7/2) (7/20)=
    (1/((7/20:ℝ)^3*sqrt (7/20))-1+(7/2)*(7/20-1))/(1-7/20)^2 := by
  unfold NegativePowerHermite.coefficient
  rw [rpow_neg (by norm_num : (0:ℝ)≤7/20),CurvatureBudget.rpow_seven_halves (by norm_num : (0:ℝ)<7/20)]
  simp only [one_div]

theorem tail_eq (p : Parameters) {m : ℝ} (hm : 0<m) :
    tail p m=CurvatureErrorLayerBudget.centralTail m p.vmin p.vmax := by
  unfold tail powerExpCost CurvatureErrorLayerBudget.centralTail
  rw [show (-1/2:ℝ)=-(1/2:ℝ) by ring,rpow_neg hm.le,←sqrt_eq_rpow]
  ring

theorem centralError_eq (p : Parameters) {m : ℝ} (hm : 0<m) :
    ShiftedCurvatureErrorLayerBudget.centralError (7/20) m p.vmin p.vmax p.eta p.D=
      cubic p m+quartic p m+triangular p m+tail p m := by
  rw [tail_eq p hm]
  rfl

noncomputable def sqrtExpression (p : Parameters) (m : ℝ) : ℝ :=
  shiftFactor p.start (1/(6*p.vmin))*main p m-
  (4*sqrt (2*Real.pi)/(3*Real.pi))*p.eta*rho (7/20) m^3*
    (1+(680/49)*p.D/m)/sqrt (p.vmin*m)-
  (5/16)*rho (7/20) m^3*sqrt (rho (7/20) m)*
    (1+((1/((7/20:ℝ)^2*sqrt (7/20))-1+(5/2)*(7/20-1))/(1-7/20)^2)*p.D/m)/(p.vmin*m)-
  (1+((1/((7/20:ℝ)^3*sqrt (7/20))-1+(7/2)*(7/20-1))/(1-7/20)^2)*p.D/m)/(96*(p.vmin*m)^2)-
  CurvatureErrorLayerBudget.centralTail m p.vmin p.vmax-
  (sqrt (2*Real.pi)*p.vmax*sqrt p.vmax*(m*sqrt m)*exp (-p.badRate 0*m)+
    (1/(cut 22*sqrt (cut 22)))*exp (-p.badRate 23*m)+
      ∑i : Fin 22,(1/(cut i.val*sqrt (cut i.val))-1/(cut (i.val+1)*sqrt (cut (i.val+1))))*
        exp (-p.badRate ⟨i.val+1,by omega⟩*m))

theorem budget_eq_sqrtExpression (p : Parameters) {m : ℝ} (hm : 6≤m) :
    budget p m=sqrtExpression p m := by
  have hm0 : 0<m := by linarith
  have hr:=rho_pos (show 1<(7/20:ℝ)*m by linarith)
  unfold budget cubic quartic triangular bad momentFactor
  rw [coefficient_two,coefficient_five_halves,coefficient_seven_halves,
    CurvatureBudget.rpow_seven_halves hr,tail_eq p hm0]
  simp_rw [rpow_neg_three_halves (cut_pos _)]
  unfold powerExpCost
  rw [rpow_three_halves hm0]
  unfold sqrtExpression
  ring

#print axioms budget_eq_sqrtExpression
#print axioms centralError_eq
end ForestUnimodality.Stage350CurvatureBudget
