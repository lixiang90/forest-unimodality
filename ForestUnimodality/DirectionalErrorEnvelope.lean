import ForestUnimodality.BinomialDirectionalError
import ForestUnimodality.PointMassErrorEnvelope

/-! Uniform negative-power prices for the same zeroth and second Fourier
error moments used in the signed directional comparison. -/
namespace ForestUnimodality.DirectionalErrorEnvelope
open Real BinomialDirectionalError PointMassErrorEnvelope

theorem half_power {x : ℝ} (hx : 0<x) (n : ℕ) :
    x^((n:ℝ)+1/2)=x^n*sqrt x := by
  rw [rpow_add hx,rpow_natCast,←sqrt_eq_rpow]

theorem raw_quartic_zero {x y v : ℝ} (hx : 0<x) (hy : 0<y) (hv : 0<v) :
    x*v/(16*sqrt (2*Real.pi)*(y*v)^2*sqrt (y*v))=
      (x/y)^(5/2:ℝ)/(16*sqrt (2*Real.pi)*(x*v)^(3/2:ℝ)) := by
  rw [show (5/2:ℝ)=(2:ℕ)+1/2 by norm_num,
    show (3/2:ℝ)=(1:ℕ)+1/2 by norm_num,
    half_power (div_pos hx hy),half_power (mul_pos hx hv),pow_one,
    sqrt_div hx.le,sqrt_mul hy.le,sqrt_mul hx.le,div_pow,mul_pow]
  have hxS: sqrt x≠0 := (sqrt_pos.mpr hx).ne'
  have hyS: sqrt y≠0 := (sqrt_pos.mpr hy).ne'
  have hvS: sqrt v≠0 := (sqrt_pos.mpr hv).ne'
  field_simp

theorem raw_quartic_two {x y v : ℝ} (hx : 0<x) (hy : 0<y) (hv : 0<v) :
    5*x*v/(16*sqrt (2*Real.pi)*(y*v)^3*sqrt (y*v))=
      5*(x/y)^(7/2:ℝ)/(16*sqrt (2*Real.pi)*(x*v)^(5/2:ℝ)) := by
  rw [show (7/2:ℝ)=(3:ℕ)+1/2 by norm_num,
    show (5/2:ℝ)=(2:ℕ)+1/2 by norm_num,
    half_power (div_pos hx hy),half_power (mul_pos hx hv),
    sqrt_div hx.le,sqrt_mul hy.le,sqrt_mul hx.le,div_pow,mul_pow,mul_pow]
  have hxS: sqrt x≠0 := (sqrt_pos.mpr hx).ne'
  have hyS: sqrt y≠0 := (sqrt_pos.mpr hy).ne'
  have hvS: sqrt v≠0 := (sqrt_pos.mpr hv).ne'
  field_simp

theorem errorZero_eq (M : ℕ) (hM : 2≤M) {q : ℝ} (hv : 0<q*(1-q)) :
    errorZero M q=
      |1-2*q| *((M:ℝ)/((M:ℝ)-1))^2/(3*Real.pi*((M:ℝ)*(q*(1-q))))+
      ((M:ℝ)/((M:ℝ)-1))^(5/2:ℝ)/
        (16*sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(3/2:ℝ))+
      gaussianZero ((M:ℝ)*(q*(1-q))) := by
  have hx : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hy : 0<((M-1:ℕ):ℝ) := by exact_mod_cast (show 0<M-1 by omega)
  have hc : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤M)];norm_num
  dsimp only [errorZero,centralZero]
  rw [raw_quartic_zero hx hy hv,hc]
  congr 2
  field_simp

theorem errorTwo_eq (M : ℕ) (hM : 2≤M) {q : ℝ} (hv : 0<q*(1-q)) :
    errorTwo M q=
      4*|1-2*q| *((M:ℝ)/((M:ℝ)-1))^3/(3*Real.pi*((M:ℝ)*(q*(1-q)))^2)+
      5*((M:ℝ)/((M:ℝ)-1))^(7/2:ℝ)/
        (16*sqrt (2*Real.pi)*((M:ℝ)*(q*(1-q)))^(5/2:ℝ))+
      gaussianTwo ((M:ℝ)*(q*(1-q))) := by
  have hx : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hy : 0<((M-1:ℕ):ℝ) := by exact_mod_cast (show 0<M-1 by omega)
  have hc : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤M)];norm_num
  dsimp only [errorTwo,centralTwo]
  rw [raw_quartic_two hx hy hv,hc]
  congr 2
  field_simp

theorem gaussianZero_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    gaussianZero b≤gaussianZero a := by
  have hb:=ha.trans_le hab
  unfold gaussianZero
  apply div_le_div₀ (by positivity) ?_ (by positivity) (by gcongr)
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg Real.pi)]

theorem gaussianTwo_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    gaussianTwo b≤gaussianTwo a := by
  have hb:=ha.trans_le hab
  have h1 : 1/b≤1/a := one_div_le_one_div_of_le ha hab
  have h2 : 1/(Real.pi^2*b^2)≤1/(Real.pi^2*a^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have he : exp (-b*Real.pi^2/2)≤exp (-a*Real.pi^2/2) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg Real.pi)]
  exact mul_le_mul (add_le_add h1 h2) he (exp_pos _).le (by positivity)

noncomputable def costTwo (alpha m v eta : ℝ) : ℝ :=
  (4*eta*rho alpha m^3/(3*Real.pi))/(v*m)^2

noncomputable def costFiveHalves (alpha m v : ℝ) : ℝ :=
  (5*rho alpha m^(7/2:ℝ)/(16*sqrt (2*Real.pi)))/(v*m)^(5/2:ℝ)

theorem errorZero_le (M : ℕ) {q alpha m v eta : ℝ}
    (hm : 0<m) (ham : 1<alpha*m) (hM : alpha*m≤(M:ℝ))
    (hv : 0<v) (hvq : v≤q*(1-q)) (heta : |1-2*q|≤eta) :
    errorZero M q≤costOne alpha m v eta*((M:ℝ)/m)^(-1:ℝ)+
      costThreeHalves alpha m v*((M:ℝ)/m)^(-(3/2:ℝ))+
      gaussianZero (v*(alpha*m)) := by
  have hM1 : 1<M := by exact_mod_cast (ham.trans_le hM)
  have hM0 : 0<(M:ℝ) := by linarith
  rw [errorZero_eq M (by omega) (hv.trans_le hvq)]
  exact add_le_add
    (add_le_add (first_cost_bound hm ham hM hv hvq (abs_nonneg _) heta)
      (second_cost_bound hm ham hM hv hvq))
    (gaussianZero_antitone (a:=v*(alpha*m)) (b:=(M:ℝ)*(q*(1-q))) (by positivity) (by
      nlinarith [mul_le_mul hM hvq hv.le hM0.le]))

theorem errorTwo_le (M : ℕ) {q alpha m v eta : ℝ}
    (hm : 0<m) (ham : 1<alpha*m) (hM : alpha*m≤(M:ℝ))
    (hv : 0<v) (hvq : v≤q*(1-q)) (heta : |1-2*q|≤eta) :
    errorTwo M q≤costTwo alpha m v eta*((M:ℝ)/m)^(-2:ℝ)+
      costFiveHalves alpha m v*((M:ℝ)/m)^(-(5/2:ℝ))+
      gaussianTwo (v*(alpha*m)) := by
  have hM1 : 1<M := by exact_mod_cast (ham.trans_le hM)
  have hM0 : 0<(M:ℝ) := by linarith
  have hv0:=hv.trans_le hvq
  have hMsub : 0<(M:ℝ)-1 := by linarith
  have hr : 0≤(M:ℝ)/((M:ℝ)-1) := by positivity
  have hR:=rho_pos ham
  have hRle : (M:ℝ)/((M:ℝ)-1)≤rho alpha m := rho_antitone ham hM
  have heta0:=(abs_nonneg (1-2*q)).trans heta
  have hcost2 : costTwo alpha m v eta*((M:ℝ)/m)^(-2:ℝ)=
      (4*eta*rho alpha m^3/(3*Real.pi))/((M:ℝ)*v)^2 := by
    unfold costTwo
    rw [←rpow_two (v*m),scaled_power_cost hM0 hm hv,rpow_two]
  have hcost52 : costFiveHalves alpha m v*((M:ℝ)/m)^(-(5/2:ℝ))=
      (5*rho alpha m^(7/2:ℝ)/(16*sqrt (2*Real.pi)))/((M:ℝ)*v)^(5/2:ℝ) := by
    unfold costFiveHalves
    rw [scaled_power_cost hM0 hm hv]
  rw [errorTwo_eq M (by omega) hv0,hcost2,hcost52]
  apply add_le_add
  · apply add_le_add
    · rw [div_div]
      apply div_le_div₀ (by positivity) ?_ (by positivity) ?_ <;> gcongr
    · rw [div_div]
      apply div_le_div₀ (by positivity) ?_ (by positivity) ?_ <;> gcongr
  · exact gaussianTwo_antitone (a:=v*(alpha*m)) (b:=(M:ℝ)*(q*(1-q))) (by positivity) (by
      nlinarith [mul_le_mul hM hvq hv.le hM0.le])

#print axioms errorZero_le
#print axioms errorTwo_le
end ForestUnimodality.DirectionalErrorEnvelope
