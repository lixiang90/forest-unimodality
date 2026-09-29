import ForestUnimodality.ForestSourceCertificate
import ForestUnimodality.ElementaryEnclosure
import ForestUnimodality.QuadraticCertificate

/-! The first official stage-350 source parameters. The endpoint and interior
cells are continuous-domain statements. No full-domain certificate is asserted
until every probability cell is covered. -/
namespace ForestUnimodality

noncomputable def sourceParameters_22_25_1 : SourceRowParameters where
  A := 14896533/50000000
  C := 3577121/5000000
  positivePrice := fun a => if a = 1 then 10854739/50000000 else 1729251/5000000
  negativePrice := fun a => if a = 1 then 11742489/25000000 else 24188011/100000000
  phiPrice := 0
  responsePrice := 96780649/100000000
  blockingPrice := 89615257/100000000
  logPrice := 240111/2000000

theorem sourceParameters_22_25_1_admissible : sourceParameters_22_25_1.Admissible := by
  refine ⟨by norm_num [sourceParameters_22_25_1], by norm_num [sourceParameters_22_25_1],
    by norm_num [sourceParameters_22_25_1], ?_, ?_⟩ <;>
    intro a <;> simp only [sourceParameters_22_25_1] <;> split <;> norm_num

private theorem log_25_11_le : Real.log (25/11 : ℝ) ≤ 823/1000 := by
  have hc : ExpEnclosure.smallCheck (823/1000) 10 (25/11) 3 = true := by decide +kernel
  have he := (ExpEnclosure.smallCheck_sound hc).1
  norm_num at he
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (by norm_num : (0:ℝ) < 25/11)]
  exact he

private theorem source_leaf_log :
    Real.log (1/2 : ℝ) - 2*Real.log (1-(1/2:ℝ)) - Real.log (22/25:ℝ) =
      Real.log (25/11:ℝ) := by
  have he : (25/11:ℝ) = ((1/2)*(22/25))⁻¹ := by norm_num
  rw [he, Real.log_inv, Real.log_mul (by norm_num) (by norm_num)]
  norm_num
  ring

/-- All three allowed source/parent states, every real retention in its
true interval, at the actual leaf endpoint p=q and z=a. -/
theorem source_row_22_25_1_leaf {a parentA r : ℝ}
    (hs : SourceMarkState a parentA) (hr : (2/3:ℝ) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA (1/2) r a := by
  have hg := log_25_11_le
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp only [sourceScalarRow, sourceParameters_22_25_1, source_leaf_log] <;>
    norm_num <;> nlinarith

private theorem log_three_le : Real.log (3:ℝ) ≤ 10987/10000 := by
  let cert : ExpEnclosure.PowerCertificate := ⟨2, 10987/20000, 12, 17321/10000, 2⟩
  have hc : cert.check (10987/10000) 3 4 = true := by decide +kernel
  have he := (cert.check_sound hc).1
  norm_num at he
  apply Real.exp_le_exp.mp
  rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)]

private theorem odds_capacity_one_log {x:ℝ} (hx : 2 ≤ x) (hx4 : x < 4) :
    sourceOddsCapacity 1 (Real.log x) = x/2 := by
  have hxpos : 0 < x := by linarith
  have hL : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hf : Nat.floor (Real.log x / Real.log (2:ℝ)) = 1 := by
    apply (Nat.floor_eq_iff (div_nonneg hlog hL.le)).mpr
    constructor
    · apply (le_div_iff₀ hL).mpr
      simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) hx
    · apply (div_lt_iff₀ hL).mpr
      have hh := Real.log_lt_log hxpos hx4
      have h4 : Real.log (4:ℝ) = 2*Real.log (2:ℝ) := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      rw [h4] at hh
      norm_num only [Nat.cast_one, one_add_one_eq_two]
      exact hh
  simp only [sourceOddsCapacity, one_add_one_eq_two, hf, Nat.cast_one, one_mul,
    Real.exp_sub, Real.exp_log hxpos, Real.exp_log (by norm_num : (0:ℝ)<2)]
  ring

private theorem cell_log_bonus {p : ℝ} (hpl : 1/4 ≤ p) (hph : p ≤ 25001/100000) :
    (327/1000:ℝ) ≤ -(240111/2000000) *
      (Real.log p - 2*Real.log (1-p) - Real.log (22/25:ℝ)) / p := by
  have hp : 0 < p := by linarith
  have hp1 : 0 < 1-p := by linarith
  have hc : ExpEnclosure.smallCheck (-341/500) 12
      ((25001/100000) / ((1-25001/100000)^2*(22/25))) 1 = true := by decide +kernel
  have he := (ExpEnclosure.smallCheck_sound hc).1
  norm_num at he
  have hlog : Real.log ((25001/100000:ℝ) / ((1-25001/100000)^2*(22/25))) ≤ -341/500 := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (by norm_num)]
    norm_num
    exact he
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hlog
  have h1 := Real.log_le_log hp hph
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<1-25001/100000)
    (show 1-(25001/100000:ℝ) ≤ 1-p by linarith)
  have hnum : Real.log p - 2*Real.log (1-p) - Real.log (22/25:ℝ) ≤ -341/500 := by
    linarith
  apply (le_div_iff₀ hp).mpr
  nlinarith

private theorem cell_capacity_bounds {p : ℝ} (hpl : 1/4 ≤ p) (hph : p ≤ 25001/100000) :
    (91/25:ℝ) ≤ 1 / (p*sourceLogCapacity 1 p) ∧
    (2/3:ℝ) ≤ 1 / sourceOddsCapacity 1 (sourceLogCapacity 1 p) := by
  have hp : 0 < p := by linarith
  have hx2 : 2 ≤ (1-p)/p := (le_div_iff₀ hp).mpr (by linarith)
  have hx3 : (1-p)/p ≤ 3 := (div_le_iff₀ hp).mpr (by linarith)
  have hT : sourceLogCapacity 1 p = Real.log ((1-p)/p) := by simp [sourceLogCapacity]
  have hTpos : 0 < sourceLogCapacity 1 p := by rw [hT]; exact Real.log_pos (by linarith)
  have hTupper : sourceLogCapacity 1 p ≤ 10987/10000 := by
    rw [hT]
    exact (Real.log_le_log (by linarith) hx3).trans log_three_le
  constructor
  · apply (le_div_iff₀ (mul_pos hp hTpos)).mpr
    have he := mul_le_mul hph hTupper hTpos.le (by norm_num : (0:ℝ) ≤ 25001/100000)
    nlinarith
  · rw [hT, odds_capacity_one_log hx2 (by linarith)]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<((1-p)/p)/2)).mpr
    linarith

/-- A rational lower envelope on the entire first interior cell. -/
noncomputable def sourceCaseOneEnvelope (a parentA r z : ℝ) : ℝ :=
  let P := sourceParameters_22_25_1
  r*(P.A+P.C*a)-r*(3/4)*z^2+327/1000 +
    P.positivePrice a*(91/25)*(max 0 (a-z))^2-
    P.positivePrice parentA*(7/8)*(max 0 z)^2+
    P.negativePrice a*(91/25)*(max 0 (z-a))^2-
    P.negativePrice parentA*(7/8)*(max 0 (-z))^2+
    P.responsePrice*(z-r*a)+
    P.blockingPrice*(r*((a-z)^2*(2/3))-(1-r)*(3/4)*z^2)

private theorem cell_envelope_le {a parentA p r z : ℝ}
    (hpl : 1/4 ≤ p) (hph : p ≤ 25001/100000) (hr : (4/7:ℝ) ≤ r) (hr1 : r ≤ 1) :
    sourceCaseOneEnvelope a parentA r z ≤
      sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have hr0 : 0 ≤ r := by linarith
  have hrc : 0 ≤ 1-r := by linarith
  have hcap := cell_capacity_bounds hpl hph
  have hlog := cell_log_bonus hpl hph
  have hu := sourceParameters_22_25_1_admissible.2.2.2.1
  have hv := sourceParameters_22_25_1_admissible.2.2.2.2
  have hmain : r*(1-p)*z^2 ≤ r*(3/4)*z^2 := by gcongr; linarith
  have hup : sourceParameters_22_25_1.positivePrice a*(91/25)*(max 0 (a-z))^2 ≤
      sourceParameters_22_25_1.positivePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (a-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hu a)) (sq_nonneg _)
  have hvp : sourceParameters_22_25_1.negativePrice a*(91/25)*(max 0 (z-a))^2 ≤
      sourceParameters_22_25_1.negativePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (z-a))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hv a)) (sq_nonneg _)
  have hum : sourceParameters_22_25_1.positivePrice parentA*(1-p/2)*(max 0 z)^2 ≤
      sourceParameters_22_25_1.positivePrice parentA*(7/8)*(max 0 z)^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-p/2 ≤ (7/8:ℝ)) (hu parentA)) (sq_nonneg _)
  have hvm : sourceParameters_22_25_1.negativePrice parentA*(1-p/2)*(max 0 (-z))^2 ≤
      sourceParameters_22_25_1.negativePrice parentA*(7/8)*(max 0 (-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-p/2 ≤ (7/8:ℝ)) (hv parentA)) (sq_nonneg _)
  have hblock : r*((a-z)^2*(2/3))-(1-r)*(3/4)*z^2 ≤
      r*((a-z)^2/sourceOddsCapacity 1 (sourceLogCapacity 1 p))-(1-r)*(1-p)*z^2 := by
    rw [div_eq_mul_one_div ((a-z)^2)]
    apply sub_le_sub
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcap.2 (sq_nonneg _)) hr0
    · gcongr
      linarith
  have hb := mul_le_mul_of_nonneg_left hblock sourceParameters_22_25_1_admissible.2.2.1
  dsimp only [sourceCaseOneEnvelope, sourceScalarRow]
  have hw : sourceParameters_22_25_1.phiPrice = 0 := rfl
  rw [hw, zero_mul]
  have hell : sourceParameters_22_25_1.logPrice = 240111/2000000 := rfl
  rw [hell]
  rw [neg_mul, neg_div] at hlog
  linarith

private theorem envelope_00_lo (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 0 0 (4/7) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (56449731917/84000000000) (-96780649/100000000) (43509033/87500000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (42545088959/210000000000) (96780649/100000000) (43509033/87500000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_00_hi (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 0 0 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (10736216141/12000000000) (-96780649/100000000) (31246533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (6378895831/15000000000) (96780649/100000000) (31246533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_01_lo (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 0 1 (4/7) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (19852501171/42000000000) (-96780649/100000000) (43509033/87500000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (8275487173/26250000000) (96780649/100000000) (43509033/87500000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_01_hi (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 0 1 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (2086027979/3000000000) (-96780649/100000000) (31246533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (16137621437/30000000000) (96780649/100000000) (31246533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_10_lo (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 1 0 (4/7) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have haz : 0 ≤ 1-z := by linarith
    have hza : z-1 ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (85407373489/420000000000) (68009886991/52500000000) (38971907479/26250000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn, max_eq_right haz, max_eq_left hza] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    by_cases hz1 : z ≤ 1
    · have haz : 0 ≤ 1-z := by linarith
      have hza : z-1 ≤ 0 := by linarith
      have hc : QuadraticCertificate.rayCheck (23599182707/210000000000) (1498941217/1400000000) (844465261/2800000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (1-z)) (by simpa using haz)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_right haz, max_eq_left hza] ; ring
    · have haz : 1-z ≤ 0 := by linarith
      have hza : 0 ≤ z-1 := by linarith
      have hc : QuadraticCertificate.rayCheck (216690276539/210000000000) (-1498941217/1400000000) (844465261/2800000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (z-1)) (by simpa using hza)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_left haz, max_eq_right hza] ; ring

private theorem envelope_10_hi (z : ℝ) :
    0 ≤ sourceCaseOneEnvelope 1 0 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have haz : 0 ≤ 1-z := by linarith
    have hza : z-1 ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (25560896977/60000000000) (13556352013/7500000000) (13201563119/7500000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn, max_eq_right haz, max_eq_left hza] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    by_cases hz1 : z ≤ 1
    · have haz : 0 ≤ 1-z := by linarith
      have hza : z-1 ≤ 0 := by linarith
      have hc : QuadraticCertificate.rayCheck (5025616813/15000000000) (3554473/3125000) (57547187/200000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (1-z)) (by simpa using haz)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_right haz, max_eq_left hza] ; ring
    · have haz : 1-z ≤ 0 := by linarith
      have hza : 0 ≤ z-1 := by linarith
      have hc : QuadraticCertificate.rayCheck (18817837801/15000000000) (-3554473/3125000) (57547187/200000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (z-1)) (by simpa using hza)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOneEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_left haz, max_eq_right hza] ; ring

private theorem envelope_nonneg {a parentA r z : ℝ}
    (hs : SourceMarkState a parentA) (hr : (4/7:ℝ) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceCaseOneEnvelope a parentA r z := by
  have hlo : 0 ≤ sourceCaseOneEnvelope a parentA (4/7) z := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact envelope_00_lo z
    · exact envelope_01_lo z
    · exact envelope_10_lo z
  have hhi : 0 ≤ sourceCaseOneEnvelope a parentA 1 z := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact envelope_00_hi z
    · exact envelope_01_hi z
    · exact envelope_10_hi z
  have he : sourceCaseOneEnvelope a parentA r z =
      ((1-r)/(1-4/7))*sourceCaseOneEnvelope a parentA (4/7) z +
      ((r-4/7)/(1-4/7))*sourceCaseOneEnvelope a parentA 1 z := by
    unfold sourceCaseOneEnvelope
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (by positivity) hlo) (mul_nonneg (by positivity) hhi)

/-- Full continuous response and retention coverage on one actual interior
probability cell, with all transcendental comparisons proved in Lean. -/
theorem source_row_22_25_1_cell {a parentA p r z : ℝ}
    (hs : SourceMarkState a parentA) (hpl : 1/4 ≤ p) (hph : p ≤ 25001/100000)
    (hr : 1/(1+1*(1-p)) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have hden : 0 < 1+1*(1-p) := by linarith
  have hr0 : (4/7:ℝ) ≤ r := by
    apply le_trans ?_ hr
    apply (le_div_iff₀ hden).mpr
    linarith
  exact (envelope_nonneg hs hr0 hr1).trans (cell_envelope_le hpl hph hr0 hr1)

#print axioms source_row_22_25_1_cell

#print axioms source_row_22_25_1_leaf
end ForestUnimodality





