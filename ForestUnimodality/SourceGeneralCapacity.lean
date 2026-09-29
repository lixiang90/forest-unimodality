import ForestUnimodality.SourceScalarBounds

/-! Uniform real capacity, logarithmic and occupation-potential bounds for
arbitrary positive activity endpoints. All interval assertions cover real
probabilities; no floating-point floor or positive grid cutoff is used. -/
namespace ForestUnimodality

theorem sourceOddsCapacity_log_pow {b x : ℝ} (hb : 0 < b) (j : ℕ)
    (hxlo : (1+b)^j ≤ x) (hxhi : x < (1+b)^(j+1)) :
    sourceOddsCapacity b (Real.log x) = (j:ℝ)*b+x/(1+b)^j-1 := by
  have hB : 0 < 1+b := by linarith
  have hx : 0 < x := (pow_pos hB j).trans_le hxlo
  have hL : 0 < Real.log (1+b) := Real.log_pos (by linarith)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg ((one_le_pow₀ (by linarith : (1:ℝ)≤1+b)).trans hxlo)
  have hf : Nat.floor (Real.log x / Real.log (1+b)) = j := by
    apply (Nat.floor_eq_iff (div_nonneg hlog hL.le)).mpr
    constructor
    · apply (le_div_iff₀ hL).mpr
      have h := Real.log_le_log (pow_pos hB j) hxlo
      simpa only [Real.log_pow] using h
    · apply (div_lt_iff₀ hL).mpr
      have h := Real.log_lt_log hx hxhi
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h
  have hexp : Real.exp (Real.log x-(j:ℝ)*Real.log (1+b)) = x/(1+b)^j := by
    rw [← Real.log_pow, Real.exp_sub, Real.exp_log hx, Real.exp_log (pow_pos hB j)]
  simp only [sourceOddsCapacity, hf, hexp]

theorem source_cell_capacity_bounds_general {b K pl ph p tUpper L H : ℝ} (j : ℕ)
    (hb : 0 < b) (hK : 0 < K) (hbexp : b ≤ K*Real.exp (1+K))
    (hpl : 0 < pl) (hplp : pl ≤ p) (hpph : p ≤ ph) (hpq : p < b/(1+b))
    (hlog : Real.log (b*(1-pl)/pl) ≤ tUpper)
    (hL : L ≤ 1/K ∨ L*(ph*tUpper) ≤ 1) (hL0 : 0 ≤ L)
    (hjlo : (1+b)^j ≤ b*(1-pl)/pl) (hjhi : b*(1-pl)/pl < (1+b)^(j+1))
    (hH : H*((j:ℝ)*b+(b*(1-pl)/pl)/(1+b)^j-1) ≤ 1) :
    L ≤ 1/(p*sourceLogCapacity b p) ∧
      H ≤ 1/sourceOddsCapacity b (sourceLogCapacity b p) := by
  have hp : 0 < p := hpl.trans_le hplp
  have hp1 : p < 1 := hpq.trans ((div_lt_one (by linarith : 0<1+b)).mpr (by linarith))
  have hratio : b*(1-p)/p ≤ b*(1-pl)/pl := by
    apply (div_le_div_iff₀ hp hpl).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hplp)]
  have hratioPos : 0 < b*(1-p)/p := div_pos (mul_pos hb (sub_pos.mpr hp1)) hp
  have hTpos := source_log_capacity_pos hb hp hpq
  have hTle : sourceLogCapacity b p ≤ Real.log (b*(1-pl)/pl) :=
    Real.log_le_log hratioPos hratio
  constructor
  · rcases hL with hL | hL
    · exact hL.trans (source_capacity_reciprocal_lower hb hK hp hpq hbexp)
    · apply (le_div_iff₀ (mul_pos hp hTpos)).mpr
      have hprod := mul_le_mul hpph (hTle.trans hlog) hTpos.le (hp.le.trans hpph)
      exact (mul_le_mul_of_nonneg_left hprod hL0).trans hL
  · have hHpos := sourceOddsCapacity_pos hb hTpos
    have hHle := sourceOddsCapacity_mono hb hTpos.le hTle
    rw [sourceOddsCapacity_log_pow hb j hjlo hjhi] at hHle
    have hHLpos : 0 < (j:ℝ)*b+(b*(1-pl)/pl)/(1+b)^j-1 := hHpos.trans_le hHle
    exact ((le_div_iff₀ hHLpos).mpr hH).trans (one_div_le_one_div_of_le hHpos hHle)

/-- Tangent-log estimate on a whole interval whose left endpoint is zero. -/
theorem source_probability_log_capacity_le_endpoint {b p δ : ℝ}
    (hb : 0 < b) (hp : 0 < p) (hpδ : p ≤ δ) (hδ1 : δ < 1)
    (hT : 1/(1-δ) ≤ sourceLogCapacity b δ) :
    p*sourceLogCapacity b p ≤ δ*sourceLogCapacity b δ := by
  have hδ : 0 < δ := hp.trans_le hpδ
  have hp1 : p < 1 := hpδ.trans_lt hδ1
  have hrp : 0 < b*(1-p)/p := div_pos (mul_pos hb (sub_pos.mpr hp1)) hp
  have hrδ : 0 < b*(1-δ)/δ := div_pos (mul_pos hb (sub_pos.mpr hδ1)) hδ
  have hlog := Real.log_le_sub_one_of_pos (div_pos hrp hrδ)
  rw [Real.log_div hrp.ne' hrδ.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have he : p*((b*(1-p)/p)/(b*(1-δ)/δ)-1) = (δ-p)/(1-δ) := by
    field_simp [hb.ne', hp.ne', hδ.ne', (sub_pos.mpr hδ1).ne']
    ring
  rw [he] at hmul
  have hmono := mul_le_mul_of_nonneg_left hT (sub_nonneg.mpr hpδ)
  dsimp only [sourceLogCapacity] at hT hmono ⊢
  rw [mul_one_div] at hmono
  linarith

theorem source_origin_capacity_lower {b p δ tUpper L : ℝ}
    (hb : 0 < b) (hp : 0 < p) (hpδ : p ≤ δ) (hδq : δ < b/(1+b))
    (hT : 1/(1-δ) ≤ sourceLogCapacity b δ)
    (hlog : sourceLogCapacity b δ ≤ tUpper) (hL : 0 ≤ L) (hbound : L*(δ*tUpper) ≤ 1) :
    L ≤ 1/(p*sourceLogCapacity b p) := by
  have hδ : 0 < δ := hp.trans_le hpδ
  have hδ1 : δ < 1 := hδq.trans ((div_lt_one (by linarith : 0<1+b)).mpr (by linarith))
  have hc := (source_probability_log_capacity_le_endpoint hb hp hpδ hδ1 hT).trans
    (mul_le_mul_of_nonneg_left hlog hδ.le)
  apply (le_div_iff₀ (mul_pos hp (source_log_capacity_pos hb hp (hpδ.trans_lt hδq)))).mpr
  exact (mul_le_mul_of_nonneg_left hc hL).trans hbound

theorem source_cell_log_bonus_general {lower ell pl ph p up low lowerLow B : ℝ}
    (hell : 0 ≤ ell) (hpl : 0 < pl) (hplp : pl ≤ p) (hpph : p ≤ ph) (hph1 : ph < 1)
    (hu : Real.log ph ≤ up) (hl : low ≤ Real.log (1-ph))
    (hLower : lowerLow ≤ Real.log lower)
    (hB : B ≤ (-ell*(up-2*low-lowerLow)) /
      (if 0 ≤ -ell*(up-2*low-lowerLow) then ph else pl)) :
    B ≤ -ell*(Real.log p-2*Real.log (1-p)-Real.log lower)/p := by
  have hp : 0 < p := hpl.trans_le hplp
  have hlogp := (Real.log_le_log hp hpph).trans hu
  have hlogc := hl.trans (Real.log_le_log (sub_pos.mpr hph1) (by linarith : 1-ph ≤ 1-p))
  let N := -ell*(up-2*low-lowerLow)
  have hN : N ≤ -ell*(Real.log p-2*Real.log (1-p)-Real.log lower) := by
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hell)
  have hlast := div_le_div_of_nonneg_right hN hp.le
  change B ≤ N/(if 0 ≤ N then ph else pl) at hB
  by_cases hn : 0 ≤ N
  · rw [if_pos hn] at hB
    exact (hB.trans (div_le_div_of_nonneg_left hn hp hpph)).trans hlast
  · rw [if_neg hn] at hB
    have hdiv : N/pl ≤ N/p := by
      apply (div_le_div_iff₀ hpl hp).mpr
      exact mul_le_mul_of_nonpos_left hplp (le_of_not_ge hn)
    exact (hB.trans hdiv).trans hlast

/-- A lower bound for the occupation potential uses an upper logarithmic
denominator and a lower logarithmic numerator, with the zero branch retained. -/
theorem source_cell_phi_lower {lower b p pl ph lowerLow up low logUpper Φ : ℝ}
    (hlower : 0 < lower) (hb : 0 < b)
    (hpl : 0 < pl) (hplp : pl ≤ p) (hpph : p ≤ ph) (hph1 : ph < 1)
    (hu : Real.log ph ≤ up) (hl : low ≤ Real.log (1-ph))
    (hLower : lowerLow ≤ Real.log lower) (hLogUpper : Real.log (1+b) ≤ logUpper)
    (hΦ : Φ ≤ (b/(1+b))/logUpper*max 0 (lowerLow+low-up)) :
    Φ ≤ sourcePhi lower b p := by
  have hp : 0 < p := hpl.trans_le hplp
  have hp1 : p < 1 := hpph.trans_lt hph1
  have hLc : low ≤ Real.log (1-p) := hl.trans
    (Real.log_le_log (sub_pos.mpr hph1) (by linarith : 1-ph ≤ 1-p))
  have hLp := (Real.log_le_log hp hpph).trans hu
  have hT : lowerLow+low-up ≤ sourceLogCapacity lower p := by
    unfold sourceLogCapacity
    rw [Real.log_div (mul_ne_zero hlower.ne' (sub_pos.mpr hp1).ne') hp.ne',
      Real.log_mul hlower.ne' (sub_pos.mpr hp1).ne']
    linarith
  have hLog : 0 < Real.log (1+b) := Real.log_pos (by linarith)
  have hq : 0 ≤ b/(1+b) := div_nonneg hb.le (by linarith)
  have hden := div_le_div_of_nonneg_left hq hLog hLogUpper
  apply hΦ.trans
  exact mul_le_mul hden (max_le_max le_rfl hT) (le_max_left _ _)
    (div_nonneg hq hLog.le)

#print axioms source_cell_capacity_bounds_general
#print axioms source_origin_capacity_lower
#print axioms source_cell_log_bonus_general
#print axioms source_cell_phi_lower
end ForestUnimodality
