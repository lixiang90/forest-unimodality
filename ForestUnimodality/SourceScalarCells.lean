import ForestUnimodality.SourceScalarBounds
import ForestUnimodality.SourceEnvelopeCertificate

/-! Exact probability-cell acceptance: logarithm witnesses, rational capacity
bounds, complete response/retention envelope, and the original scalar row. -/
namespace ForestUnimodality

structure SourceLogWitness where
  lo : ℚ
  hi : ℚ
  certificate : ElementaryEnclosure.LogCertificate

def SourceLogWitness.check (w : SourceLogWitness) (q : ℚ) : Bool :=
  w.certificate.check q w.lo w.hi

def sourceCaseOneLowerLog : ℚ := -127833371509885/1000000000000000

theorem sourceCaseOneLowerLog_le : (sourceCaseOneLowerLog : ℝ) ≤ Real.log (22/25:ℝ) := by
  have hc : ExpEnclosure.smallCheck sourceCaseOneLowerLog 16 0 (22/25) = true := by decide +kernel
  have he := (ExpEnclosure.smallCheck_sound hc).2
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (by norm_num : (0:ℝ)<22/25)]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using he

structure SourceCellCertificate where
  left : ℚ
  right : ℚ
  segment : ℕ
  logRatio : SourceLogWitness
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  bounds : SourceEnvelopeBounds

def SourceCellCertificate.logNumerator (c : SourceCellCertificate) : ℚ :=
  -(240111/2000000)*(c.logRight.hi-2*c.logComplement.lo-sourceCaseOneLowerLog)

def SourceCellCertificate.Accepts (c : SourceCellCertificate) : Prop :=
  0 < c.left ∧ c.left < c.right ∧ c.right ≤ 1/2 ∧
  c.logRatio.check ((1-c.left)/c.left) = true ∧
  c.logRight.check c.right = true ∧
  c.logComplement.check (1-c.right) = true ∧
  0 ≤ c.bounds.L ∧
  (c.bounds.L ≤ 1000000/278467 ∨ c.bounds.L*(c.right*c.logRatio.hi) ≤ 1) ∧
  c.bounds.H*((c.segment:ℚ)+((1-c.left)/c.left)/2^c.segment-1) ≤ 1 ∧
  (2:ℚ)^c.segment ≤ (1-c.left)/c.left ∧ (1-c.left)/c.left < (2:ℚ)^(c.segment+1) ∧
  1-c.left/2 ≤ c.bounds.hh ∧ 1-c.left ≤ c.bounds.dd ∧
  c.bounds.rl ≤ 1/(2-c.left) ∧ 1 ≤ c.bounds.rh ∧
  c.bounds.B ≤ c.logNumerator/(if 0 ≤ c.logNumerator then c.right else c.left) ∧
  c.bounds.check = true

instance (c : SourceCellCertificate) : Decidable c.Accepts := by
  unfold SourceCellCertificate.Accepts
  infer_instance

def SourceCellCertificate.check (c : SourceCellCertificate) : Bool := decide c.Accepts

private theorem source_envelope_le {a parentA p r z L H hh dd B : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hcap : L ≤ 1/(p*sourceLogCapacity 1 p) ∧ H ≤ 1/sourceOddsCapacity 1 (sourceLogCapacity 1 p))
    (hlog : B ≤ -(240111/2000000)*(Real.log p-2*Real.log (1-p)-Real.log (22/25:ℝ))/p)
    (hhh : 1-p/2 ≤ hh) (hdd : 1-p ≤ dd) :
    sourceEnvelope L H hh dd B a parentA r z ≤
      sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have hrc : 0 ≤ 1-r := by linarith
  have hu := sourceParameters_22_25_1_admissible.2.2.2.1
  have hv := sourceParameters_22_25_1_admissible.2.2.2.2
  have hmain : r*(1-p)*z^2 ≤ r*dd*z^2 := by gcongr
  have hup : sourceParameters_22_25_1.positivePrice a*L*(max 0 (a-z))^2 ≤
      sourceParameters_22_25_1.positivePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (a-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hu a)) (sq_nonneg _)
  have hvp : sourceParameters_22_25_1.negativePrice a*L*(max 0 (z-a))^2 ≤
      sourceParameters_22_25_1.negativePrice a*(1/(p*sourceLogCapacity 1 p))*(max 0 (z-a))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap.1 (hv a)) (sq_nonneg _)
  have hum : sourceParameters_22_25_1.positivePrice parentA*(1-p/2)*(max 0 z)^2 ≤
      sourceParameters_22_25_1.positivePrice parentA*hh*(max 0 z)^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhh (hu parentA)) (sq_nonneg _)
  have hvm : sourceParameters_22_25_1.negativePrice parentA*(1-p/2)*(max 0 (-z))^2 ≤
      sourceParameters_22_25_1.negativePrice parentA*hh*(max 0 (-z))^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhh (hv parentA)) (sq_nonneg _)
  have hblock : r*((a-z)^2*H)-(1-r)*dd*z^2 ≤
      r*((a-z)^2/sourceOddsCapacity 1 (sourceLogCapacity 1 p))-(1-r)*(1-p)*z^2 := by
    rw [div_eq_mul_one_div ((a-z)^2)]
    apply sub_le_sub
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcap.2 (sq_nonneg _)) hr0
    · gcongr
  have hb := mul_le_mul_of_nonneg_left hblock sourceParameters_22_25_1_admissible.2.2.1
  dsimp only [sourceEnvelope, sourceScalarRow]
  have hw : sourceParameters_22_25_1.phiPrice = 0 := rfl
  rw [hw, zero_mul]
  have hell : sourceParameters_22_25_1.logPrice = 240111/2000000 := rfl
  rw [hell]
  rw [neg_mul, neg_div] at hlog
  have hbb : r*((a-z)^2*H) = r*(a-z)^2*H := by ring
  rw [hbb] at hb
  linarith

/-- Acceptance certifies every real response and every true retention for
all probabilities in the box. The leaf endpoint is handled separately. -/
theorem SourceCellCertificate.check_sound {c : SourceCellCertificate} (hc : c.check = true)
    {a parentA p r z : ℝ} (hs : SourceMarkState a parentA)
    (hplp : (c.left:ℝ) ≤ p) (hpph : p ≤ (c.right:ℝ)) (hpq : p < 1/2)
    (hr : 1/(1+1*(1-p)) ≤ r) (hr1 : r ≤ 1) :
    0 ≤ sourceScalarRow sourceParameters_22_25_1 (22/25) 1 a parentA p r z := by
  have h : c.Accepts := of_decide_eq_true hc
  rcases h with ⟨hpl,hplt,hph,hlogT,hlogR,hlogC,hL0,hL,hH,hjlo,hjhi,hhh,hdd,hrl,hrh,hB,hcheck⟩
  have hplr : (0:ℝ)<c.left := by exact_mod_cast hpl
  have hp : 0<p := hplr.trans_le hplp
  have hphr : (c.right:ℝ)≤1/2 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hph
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hlogTr := (c.logRatio.certificate.check_sound hlogT).2
  have hlogRr := (c.logRight.certificate.check_sound hlogR).2
  have hlogCr := (c.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogTr hlogCr
  have hLr : (c.bounds.L:ℝ) ≤ 1000000/278467 ∨
      (c.bounds.L:ℝ)*((c.right:ℝ)*(c.logRatio.hi:ℝ)) ≤ 1 := by
    rcases hL with hL | hL
    · apply Or.inl
      have hh := (Rat.cast_le (K:=ℝ)).mpr hL
      norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
      exact hh
    · apply Or.inr
      exact_mod_cast hL
  have hcap := source_cell_capacity_bounds (L:=(c.bounds.L:ℝ)) (H:=(c.bounds.H:ℝ)) (ph:=(c.right:ℝ)) (tUpper:=(c.logRatio.hi:ℝ)) c.segment hplr hplp hpph hpq hlogTr
    hLr (by exact_mod_cast hL0) (by exact_mod_cast hjlo)
    (by exact_mod_cast hjhi) (by exact_mod_cast hH)
  have hBN : (c.bounds.B:ℝ) ≤ (-(240111/2000000)*(c.logRight.hi-2*c.logComplement.lo-(sourceCaseOneLowerLog:ℝ))) /
      (if 0 ≤ -(240111/2000000:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(sourceCaseOneLowerLog:ℝ)) then (c.right:ℝ) else (c.left:ℝ)) := by
    unfold SourceCellCertificate.logNumerator at hB
    by_cases hn : 0 ≤ -(240111/2000000:ℚ)*(c.logRight.hi-2*c.logComplement.lo-sourceCaseOneLowerLog)
    · have hn' : (0:ℝ) ≤ -(240111/2000000:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(sourceCaseOneLowerLog:ℝ)) := by
        have hh := (Rat.cast_le (K:=ℝ)).mpr hn
        norm_num only [Rat.cast_zero, Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub] at hh
        exact hh
      rw [if_pos hn] at hB
      rw [if_pos hn']
      have hh := (Rat.cast_le (K:=ℝ)).mpr hB
      norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub] at hh
      exact hh
    · have hn' : ¬(0:ℝ) ≤ -(240111/2000000:ℝ)*(c.logRight.hi-2*c.logComplement.lo-(sourceCaseOneLowerLog:ℝ)) := by
        intro hh
        apply hn
        have hcast : (0:ℝ) ≤ ((-(240111/2000000:ℚ)*(c.logRight.hi-2*c.logComplement.lo-sourceCaseOneLowerLog):ℚ):ℝ) := by
          norm_num only [Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub]
          exact hh
        exact_mod_cast hcast
      rw [if_neg hn] at hB
      rw [if_neg hn']
      have hh := (Rat.cast_le (K:=ℝ)).mpr hB
      norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub] at hh
      exact hh
  have hlog := source_cell_log_bonus hplr hplp hpph (by linarith) hlogRr hlogCr sourceCaseOneLowerLog_le hBN
  have hrlr : (c.bounds.rl:ℝ) ≤ 1/(2-(c.left:ℝ)) := by exact_mod_cast hrl
  have hret : (c.bounds.rl:ℝ) ≤ r := by
    apply hrlr.trans
    apply le_trans ?_ hr
    simp only [one_mul]
    rw [show 1+(1-p)=2-p by ring]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hrhi : r ≤ (c.bounds.rh:ℝ) := hr1.trans (by exact_mod_cast hrh)
  have hr0 : 0 ≤ r := (div_nonneg (by norm_num) (by linarith : 0 ≤ 1+1*(1-p))).trans hr
  have hhh' : 1-p/2 ≤ (c.bounds.hh:ℝ) := by
    have hh : 1-(c.left:ℝ)/2≤c.bounds.hh := by exact_mod_cast hhh
    linarith
  have hdd' : 1-p ≤ (c.bounds.dd:ℝ) := by
    have hh : 1-(c.left:ℝ)≤c.bounds.dd := by exact_mod_cast hdd
    linarith
  exact (SourceEnvelopeBounds.check_sound hcheck hs hret hrhi).trans (source_envelope_le hr0 hr1 hcap hlog hhh' hdd')

#print axioms SourceCellCertificate.check_sound
end ForestUnimodality


