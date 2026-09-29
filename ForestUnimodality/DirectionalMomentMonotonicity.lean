import ForestUnimodality.DirectionalErrorLayerBudget
import ForestUnimodality.PointMassBudgetMonotonicity

/-! Infinite-scale continuation of the shared Fourier moment prices. -/
namespace ForestUnimodality.DirectionalMomentMonotonicity
open Real Set BinomialDirectionalError PointMassErrorEnvelope PointMassBudgetMonotonicity DirectionalErrorLayerBudget

noncomputable def powerMoment (p a e alpha D m : ℝ) : ℝ :=
  rho alpha m^a*momentFactor p alpha D m/m^e

theorem powerMoment_nonneg {p a e alpha D m : ℝ}
    (hp : 0≤p) (ha : 0<alpha) (hD : 0≤D) (hm : 0<m) (ham : 1<alpha*m) :
    0≤powerMoment p a e alpha D m := by
  have hr:=rho_pos ham
  have hJ:=momentFactor_nonneg hp ha hD hm
  unfold powerMoment
  positivity

theorem powerMoment_antitone {p a e alpha D x y : ℝ}
    (hp : 0≤p) (ha : 0<alpha) (hD : 0≤D) (hpow : 0≤a) (he : 0≤e)
    (hx : 0<x) (hax : 1<alpha*x) (hxy : x≤y) :
    powerMoment p a e alpha D y≤powerMoment p a e alpha D x := by
  have hy:=hx.trans_le hxy
  have hay:=hax.trans_le (mul_le_mul_of_nonneg_left hxy ha.le)
  have hr:=UnboundedBudget.bridgeRatio_antitone ha hax hxy
  change rho alpha y≤rho alpha x at hr
  have hJy:=momentFactor_nonneg hp ha hD hy
  have hJx:=momentFactor_nonneg hp ha hD hx
  have hJ:=momentFactor_antitone hp ha hD hx hxy
  unfold powerMoment
  apply div_le_div₀ (mul_nonneg (rpow_nonneg (rho_pos hax).le _) hJx) ?_ (rpow_pos_of_pos hx e) (rpow_le_rpow hx.le hxy he)
  exact mul_le_mul (rpow_le_rpow (rho_pos hay).le hr hpow) hJ hJy (rpow_nonneg (rho_pos hax).le _)

noncomputable def decayRate (alpha v : ℝ) : ℝ := Real.pi^2*v*alpha/2

noncomputable def uZero (alpha v eta D m : ℝ) : ℝ :=
  eta/(3*Real.pi*v)*powerMoment 1 2 (1/2) alpha D m+
  1/(16*sqrt (2*Real.pi)*v^(3/2:ℝ))*powerMoment (3/2) (5/2) 1 alpha D m+
  1/(Real.pi^2*v*alpha)*UnboundedBudget.powerExpCost (-1/2) (decayRate alpha v) m

noncomputable def uTwo (alpha v eta D m : ℝ) : ℝ :=
  (4*eta)/(3*Real.pi*v^2)*powerMoment 2 3 (1/2) alpha D m+
  5/(16*sqrt (2*Real.pi)*v^(5/2:ℝ))*powerMoment (5/2) (7/2) 1 alpha D m+
  (1/(v*alpha))*UnboundedBudget.powerExpCost (1/2) (decayRate alpha v) m+
  (1/(Real.pi^2*v^2*alpha^2))*UnboundedBudget.powerExpCost (-1/2) (decayRate alpha v) m

theorem uZero_nonneg {alpha v eta D m : ℝ}
    (ha : 0<alpha) (hv : 0<v) (heta : 0≤eta) (hD : 0≤D) (hm : 0<m) (ham : 1<alpha*m) :
    0≤uZero alpha v eta D m := by
  have h1:=powerMoment_nonneg (a:=2) (e:=1/2) (by norm_num : (0:ℝ)≤1) ha hD hm ham
  have h2:=powerMoment_nonneg (a:=5/2) (e:=1) (by norm_num : (0:ℝ)≤3/2) ha hD hm ham
  unfold uZero UnboundedBudget.powerExpCost
  positivity

theorem uTwo_nonneg {alpha v eta D m : ℝ}
    (ha : 0<alpha) (hv : 0<v) (heta : 0≤eta) (hD : 0≤D) (hm : 0<m) (ham : 1<alpha*m) :
    0≤uTwo alpha v eta D m := by
  have h1:=powerMoment_nonneg (a:=3) (e:=1/2) (by norm_num : (0:ℝ)≤2) ha hD hm ham
  have h2:=powerMoment_nonneg (a:=7/2) (e:=1) (by norm_num : (0:ℝ)≤5/2) ha hD hm ham
  unfold uTwo UnboundedBudget.powerExpCost
  positivity

theorem uZero_antitoneOn {alpha v eta D start : ℝ}
    (ha : 0<alpha) (hv : 0<v) (heta : 0≤eta) (hD : 0≤D)
    (hs : 0<start) (has : 1<alpha*start) :
    AntitoneOn (uZero alpha v eta D) (Ici start) := by
  intro x hx y hy hxy
  have hx0:=hs.trans_le hx
  have hax:=has.trans_le (mul_le_mul_of_nonneg_left hx ha.le)
  have hrate : 0≤decayRate alpha v := by unfold decayRate;positivity
  have hpow:=UnboundedBudget.powerExpCost_antitoneOn hs hrate
    (show (-1/2:ℝ)≤decayRate alpha v*start by nlinarith [mul_nonneg hrate hs.le]) hx hy hxy
  unfold uZero
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (powerMoment_antitone (by norm_num : (0:ℝ)≤1) ha hD
      (by norm_num) (by norm_num) hx0 hax hxy) (by positivity))
    (mul_le_mul_of_nonneg_left (powerMoment_antitone (by norm_num : (0:ℝ)≤3/2) ha hD
      (by norm_num) (by norm_num) hx0 hax hxy) (by positivity)))
    (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem uTwo_antitoneOn {alpha v eta D start : ℝ}
    (ha : 0<alpha) (hv : 0<v) (heta : 0≤eta) (hD : 0≤D)
    (hs : 0<start) (has : 1<alpha*start) (hthreshold : 1/2≤decayRate alpha v*start) :
    AntitoneOn (uTwo alpha v eta D) (Ici start) := by
  intro x hx y hy hxy
  have hx0:=hs.trans_le hx
  have hax:=has.trans_le (mul_le_mul_of_nonneg_left hx ha.le)
  have hrate : 0≤decayRate alpha v := by unfold decayRate;positivity
  have hplus:=UnboundedBudget.powerExpCost_antitoneOn hs hrate hthreshold hx hy hxy
  have hminus:=UnboundedBudget.powerExpCost_antitoneOn hs hrate
    (show (-1/2:ℝ)≤decayRate alpha v*start by nlinarith [mul_nonneg hrate hs.le]) hx hy hxy
  unfold uTwo
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (powerMoment_antitone (by norm_num : (0:ℝ)≤2) ha hD
      (by norm_num) (by norm_num) hx0 hax hxy) (by positivity))
    (mul_le_mul_of_nonneg_left (powerMoment_antitone (by norm_num : (0:ℝ)≤5/2) ha hD
      (by norm_num) (by norm_num) hx0 hax hxy) (by positivity)))
    (mul_le_mul_of_nonneg_left hplus (by positivity)))
    (mul_le_mul_of_nonneg_left hminus (by positivity))

theorem uZero_eq {alpha v eta D m : ℝ}
    (ha : 0<alpha) (hv : 0<v) (hm : 0<m) (ham : 1<alpha*m) :
    uZero alpha v eta D m=sqrt m*zeroBudget alpha m v eta D := by
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  have hr:=rho_pos ham
  have ht : sqrt m*gaussianZero (v*(alpha*m))=
      1/(Real.pi^2*v*alpha)*UnboundedBudget.powerExpCost (-1/2) (decayRate alpha v) m := by
    unfold gaussianZero UnboundedBudget.powerExpCost decayRate
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by norm_num,rpow_neg hm.le,←sqrt_eq_rpow]
    have he : -(v*(alpha*m))*Real.pi^2/2=-(Real.pi^2*v*alpha/2)*m := by ring_nf
    rw [he]
    field_simp
    rw [sq_sqrt hm.le]
  unfold zeroBudget
  rw [mul_add,mul_add,←mul_assoc,←mul_assoc,sqrt_mul_costOne hm hv,sqrt_mul_costThreeHalves hm hv,ht]
  unfold uZero powerMoment momentFactor
  rw [rpow_one,←sqrt_eq_rpow,show (2:ℝ)=(2:ℕ) by norm_num,rpow_natCast]
  ring_nf

theorem uTwo_eq {alpha v eta D m : ℝ}
    (ha : 0<alpha) (hv : 0<v) (hm : 0<m) (ham : 1<alpha*m) :
    uTwo alpha v eta D m=m*sqrt m*twoBudget alpha m v eta D := by
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  have hr:=rho_pos ham
  have hc2 : m*sqrt m*DirectionalErrorEnvelope.costTwo alpha m v eta=
      (4*eta)/(3*Real.pi*v^2)*(rho alpha m^3/sqrt m) := by
    unfold DirectionalErrorEnvelope.costTwo
    field_simp
    rw [sq_sqrt hm.le]
  have hc52 : m*sqrt m*DirectionalErrorEnvelope.costFiveHalves alpha m v=
      5/(16*sqrt (2*Real.pi)*v^(5/2:ℝ))*(rho alpha m^(7/2:ℝ)/m) := by
    unfold DirectionalErrorEnvelope.costFiveHalves
    rw [mul_rpow hv.le hm.le,show (5/2:ℝ)=(2:ℕ)+1/2 by norm_num,
      DirectionalErrorEnvelope.half_power hm]
    field_simp
  have ht : m*sqrt m*gaussianTwo (v*(alpha*m))=
      (1/(v*alpha))*UnboundedBudget.powerExpCost (1/2) (decayRate alpha v) m+
      (1/(Real.pi^2*v^2*alpha^2))*UnboundedBudget.powerExpCost (-1/2) (decayRate alpha v) m := by
    unfold gaussianTwo UnboundedBudget.powerExpCost decayRate
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by norm_num,rpow_neg hm.le,←sqrt_eq_rpow]
    have he : -(v*(alpha*m))*Real.pi^2/2=-(Real.pi^2*v*alpha/2)*m := by ring_nf
    rw [he]
    field_simp
    rw [sq_sqrt hm.le]
  unfold twoBudget
  rw [mul_add,mul_add,←mul_assoc,←mul_assoc,hc2,hc52,ht]
  unfold uTwo powerMoment momentFactor
  rw [rpow_one,←sqrt_eq_rpow,show (3:ℝ)=(3:ℕ) by norm_num,rpow_natCast]
  ring_nf

#print axioms uZero_antitoneOn
#print axioms uTwo_antitoneOn
#print axioms uZero_eq
#print axioms uTwo_eq
end ForestUnimodality.DirectionalMomentMonotonicity
