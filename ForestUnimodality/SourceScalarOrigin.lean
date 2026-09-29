import ForestUnimodality.SourceScalarCaseOne
import ForestUnimodality.SourceScalarBounds

/-! An analytic cell adjoining the singular endpoint p=0. The statement
covers every positive real p in the interval and every real response. -/
namespace ForestUnimodality

private theorem origin_log_bonus {p : ℝ} (hp : 0 < p) (hph : p ≤ 1/32) :
    (1:ℝ) ≤ -(240111/2000000) *
      (Real.log p - 2*Real.log (1-p) - Real.log (22/25:ℝ)) / p := by
  have hc : ExpEnclosure.smallCheck (-1) 12
      ((1/32) / ((1-1/32)^2*(22/25))) 1 = true := by decide +kernel
  have he := (ExpEnclosure.smallCheck_sound hc).1
  norm_num at he
  have hlog : Real.log ((1/32:ℝ) / ((1-1/32)^2*(22/25))) ≤ -1 := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (by norm_num)]
    norm_num
    exact he
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hlog
  have h1 := Real.log_le_log hp hph
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<1-1/32)
    (show 1-(1/32:ℝ) ≤ 1-p by linarith)
  have hnum : Real.log p - 2*Real.log (1-p) - Real.log (22/25:ℝ) ≤ -1 := by
    linarith
  apply (le_div_iff₀ hp).mpr
  nlinarith

private theorem origin_capacity_bounds {p : ℝ} (hp : 0 < p) (hph : p ≤ 1/32) :
    (8:ℝ) ≤ 1/(p*sourceLogCapacity 1 p) ∧
      (0:ℝ) ≤ 1/sourceOddsCapacity 1 (sourceLogCapacity 1 p) := by
  refine ⟨source_case_one_origin_capacity hp hph, ?_⟩
  have hT := source_log_capacity_pos (b:=1) (by norm_num) hp (by norm_num; linarith)
  have hH := (sourceOddsCapacity_bounds (by norm_num : (0:ℝ)<1) hT.le).1
  exact one_div_nonneg.mpr ((by positivity : (0:ℝ) ≤
    (Nat.floor (sourceLogCapacity 1 p / Real.log (1+1)) : ℝ)*1).trans hH)

noncomputable def sourceCaseOriginEnvelope (a parentA r z : ℝ) : ℝ :=
  let P := sourceParameters_22_25_1
  r*(P.A+P.C*a)-r*(1)*z^2+1 +
    P.positivePrice a*(8)*(max 0 (a-z))^2-
    P.positivePrice parentA*(1)*(max 0 z)^2+
    P.negativePrice a*(8)*(max 0 (z-a))^2-
    P.negativePrice parentA*(1)*(max 0 (-z))^2+
    P.responsePrice*(z-r*a)+
    P.blockingPrice*(r*((a-z)^2*(0))-(1-r)*(1)*z^2)

private theorem origin_envelope_le {a parentA p r z : ℝ}
    (hp : 0 < p) (hph : p ≤ 1/32) (hr : (1/2:ℝ) ≤ r) (hr1 : r ≤ 1) :
    sourceCaseOriginEnvelope a parentA r z ≤
      sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have hr0 : 0 ≤ r := by linarith
  have hrc : 0 ≤ 1-r := by linarith
  have hcap := origin_capacity_bounds hp hph
  have hlog := origin_log_bonus hp hph
  have hu := sourceParameters_22_25_1_admissible.2.2.2.1
  have hv := sourceParameters_22_25_1_admissible.2.2.2.2
  have hmain : r*(1-p)*z^2 ≤ r*(1)*z^2 := by gcongr; linarith
  have hup : sourceParameters_22_25_1.positivePrice a*(8)*(max 0 (a-z))^2 ≤
      sourceParameters_22_25_1.positivePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (a-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hu a)) (sq_nonneg _)
  have hvp : sourceParameters_22_25_1.negativePrice a*(8)*(max 0 (z-a))^2 ≤
      sourceParameters_22_25_1.negativePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (z-a))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hv a)) (sq_nonneg _)
  have hum : sourceParameters_22_25_1.positivePrice parentA*(1-p/2)*(max 0 z)^2 ≤
      sourceParameters_22_25_1.positivePrice parentA*(1)*(max 0 z)^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-p/2 ≤ (1:ℝ)) (hu parentA)) (sq_nonneg _)
  have hvm : sourceParameters_22_25_1.negativePrice parentA*(1-p/2)*(max 0 (-z))^2 ≤
      sourceParameters_22_25_1.negativePrice parentA*(1)*(max 0 (-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-p/2 ≤ (1:ℝ)) (hv parentA)) (sq_nonneg _)
  have hblock : r*((a-z)^2*(0))-(1-r)*(1)*z^2 ≤
      r*((a-z)^2/sourceOddsCapacity 1 (sourceLogCapacity 1 p))-(1-r)*(1-p)*z^2 := by
    rw [div_eq_mul_one_div ((a-z)^2)]
    apply sub_le_sub
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcap.2 (sq_nonneg _)) hr0
    · gcongr
      linarith
  have hb := mul_le_mul_of_nonneg_left hblock sourceParameters_22_25_1_admissible.2.2.1
  dsimp only [sourceCaseOriginEnvelope, sourceScalarRow]
  have hw : sourceParameters_22_25_1.phiPrice = 0 := rfl
  rw [hw, zero_mul]
  have hell : sourceParameters_22_25_1.logPrice = 240111/2000000 := rfl
  rw [hell]
  rw [neg_mul, neg_div] at hlog
  linarith


private theorem envelope_00_lo (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 0 0 (1/2) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (315369041/200000000) (-96780649/100000000) (114896533/100000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (128222879/200000000) (96780649/100000000) (114896533/100000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_00_hi (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 0 0 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (152492149/100000000) (-96780649/100000000) (64896533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (14729767/25000000) (96780649/100000000) (64896533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_01_lo (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 0 1 (1/2) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (269805151/200000000) (-96780649/100000000) (114896533/100000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (153973963/200000000) (96780649/100000000) (114896533/100000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_01_hi (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 0 1 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have hc : QuadraticCertificate.rayCheck (32427551/25000000) (-96780649/100000000) (64896533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (7179461/10000000) (96780649/100000000) (64896533/50000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := z) (by simpa using hz0)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_right hz0, max_eq_left hn] ; ring

private theorem envelope_10_lo (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 1 0 (1/2) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have haz : 0 ≤ 1-z := by linarith
    have hza : z-1 ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (109360369/200000000) (250570999/100000000) (110381297/40000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn, max_eq_right haz, max_eq_left hza] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    by_cases hz1 : z ≤ 1
    · have haz : 0 ≤ 1-z := by linarith
      have hza : z-1 ≤ 0 := by linarith
      have hc : QuadraticCertificate.rayCheck (88566351/200000000) (20250581/12500000) (69665419/100000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (1-z)) (by simpa using haz)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_right haz, max_eq_left hza] ; ring
    · have haz : 1-z ≤ 0 := by linarith
      have hza : 0 ≤ z-1 := by linarith
      have hc : QuadraticCertificate.rayCheck (492733999/200000000) (-20250581/12500000) (69665419/100000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (z-1)) (by simpa using hza)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_left haz, max_eq_right hza] ; ring

private theorem envelope_10_hi (z : ℝ) :
    0 ≤ sourceCaseOriginEnvelope 1 0 (1) z := by
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ -z := by linarith
    have haz : 0 ≤ 1-z := by linarith
    have hza : z-1 ≤ 0 := by linarith
    have hc : QuadraticCertificate.rayCheck (49487813/100000000) (250570999/100000000) (278230661/100000000) 0 = true := by decide +kernel
    have hq := QuadraticCertificate.rayCheck_sound hc (x := (-z)) (by simpa using hn)
    rw [QuadraticCertificate.evalReal_quadratic] at hq
    convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, zero_sub, sub_zero, max_eq_left hz, max_eq_right hn, max_eq_right haz, max_eq_left hza] ; ring
  · have hz0 : 0 ≤ z := by linarith
    have hn : -z ≤ 0 := by linarith
    by_cases hz1 : z ≤ 1
    · have haz : 0 ≤ 1-z := by linarith
      have hza : z-1 ≤ 0 := by linarith
      have hc : QuadraticCertificate.rayCheck (9772701/25000000) (172389391/100000000) (33375233/50000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (1-z)) (by simpa using haz)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_right haz, max_eq_left hza] ; ring
    · have haz : 1-z ≤ 0 := by linarith
      have hza : 0 ≤ z-1 := by linarith
      have hc : QuadraticCertificate.rayCheck (60293657/25000000) (-172389391/100000000) (33375233/50000000) 0 = true := by decide +kernel
      have hq := QuadraticCertificate.rayCheck_sound hc (x := (z-1)) (by simpa using hza)
      rw [QuadraticCertificate.evalReal_quadratic] at hq
      convert hq using 1 ; norm_num [sourceCaseOriginEnvelope, sourceParameters_22_25_1, max_eq_right hz0, max_eq_left hn, max_eq_left haz, max_eq_right hza] ; ring

private theorem envelope_nonneg {a parentA r z : ℝ}
    (hs : SourceMarkState a parentA) (hr : (1/2:ℝ) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceCaseOriginEnvelope a parentA r z := by
  have hlo : 0 ≤ sourceCaseOriginEnvelope a parentA (1/2) z := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact envelope_00_lo z
    · exact envelope_01_lo z
    · exact envelope_10_lo z
  have hhi : 0 ≤ sourceCaseOriginEnvelope a parentA 1 z := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact envelope_00_hi z
    · exact envelope_01_hi z
    · exact envelope_10_hi z
  have he : sourceCaseOriginEnvelope a parentA r z =
      ((1-r)/(1-1/2))*sourceCaseOriginEnvelope a parentA (1/2) z +
      ((r-1/2)/(1-1/2))*sourceCaseOriginEnvelope a parentA 1 z := by
    unfold sourceCaseOriginEnvelope
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (by positivity) hlo) (mul_nonneg (by positivity) hhi)

/-- Full continuous response and retention coverage on the whole origin
probability cell, including arbitrarily small positive real probabilities, with all transcendental comparisons proved in Lean. -/
theorem source_row_22_25_1_origin {a parentA p r z : ℝ}
    (hs : SourceMarkState a parentA) (hp : 0 < p) (hph : p ≤ 1/32)
    (hr : 1/(1+1*(1-p)) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have hden : 0 < 1+1*(1-p) := by linarith
  have hr0 : (1/2:ℝ) ≤ r := by
    apply le_trans ?_ hr
    apply (le_div_iff₀ hden).mpr
    linarith
  exact (envelope_nonneg hs hr0 hr1).trans (origin_envelope_le hp hph hr0 hr1)

#print axioms source_row_22_25_1_origin

end ForestUnimodality
