import ForestUnimodality.ForestSourceCertificate
import ForestUnimodality.ElementaryEnclosure

/-! Directed scalar bounds used to reduce source rows to rational polynomial
certificates. The probability variable is real, including arbitrarily small
positive values. -/
namespace ForestUnimodality

theorem source_log_capacity_pos {b p : ℝ} (hb : 0 < b) (hp : 0 < p)
    (hpq : p < b/(1+b)) : 0 < sourceLogCapacity b p := by
  apply Real.log_pos
  apply (lt_div_iff₀ hp).mpr
  have hh := (lt_div_iff₀ (show 0<1+b by linarith)).mp hpq
  nlinarith

/-- A global capacity bound on the open real probability interval. Its proof
uses log(x)≤x-1; the positive real K is certified by an exponential inequality. -/
theorem source_probability_log_capacity_le {b K p : ℝ}
    (hb : 0 < b) (hK : 0 < K) (hp : 0 < p) (hp1 : p < 1)
    (hcap : b ≤ K*Real.exp (1+K)) : p*sourceLogCapacity b p ≤ K := by
  have hratio : 0 < (1-p)/p := div_pos (sub_pos.mpr hp1) hp
  have hblog := Real.log_le_log hb hcap
  rw [Real.log_mul hK.ne' (Real.exp_ne_zero _), Real.log_exp] at hblog
  have hlog := Real.log_le_sub_one_of_pos (mul_pos hK hratio)
  rw [Real.log_mul hK.ne' hratio.ne'] at hlog
  have hT : sourceLogCapacity b p = Real.log b + Real.log ((1-p)/p) := by
    unfold sourceLogCapacity
    rw [show b*(1-p)/p = b*((1-p)/p) by ring,
      Real.log_mul hb.ne' hratio.ne']
  rw [hT]
  have h := mul_le_mul_of_nonneg_left (show Real.log b + Real.log ((1-p)/p) ≤
      K*((1-p)/p)+K by linarith) hp.le
  have he : p*(K*((1-p)/p)+K) = K := by field_simp; ring
  exact he ▸ h

theorem source_capacity_reciprocal_lower {b K p : ℝ}
    (hb : 0 < b) (hK : 0 < K) (hp : 0 < p) (hpq : p < b/(1+b))
    (hcap : b ≤ K*Real.exp (1+K)) :
    1/K ≤ 1/(p*sourceLogCapacity b p) := by
  have hp1 : p < 1 := hpq.trans ((div_lt_one (by linarith : 0<1+b)).mpr (by linarith))
  exact one_div_le_one_div_of_le (mul_pos hp (source_log_capacity_pos hb hp hpq))
    (source_probability_log_capacity_le hb hK hp hp1 hcap)

/-- The official first source case uses this K. Its exponential inequality
is checked over exact rationals, then transported to the real exponential. -/
theorem source_case_one_global_capacity {p : ℝ} (hp : 0 < p) (hpq : p < 1/2) :
    (1000000/278467:ℝ) ≤ 1/(p*sourceLogCapacity 1 p) := by
  let cert : ExpEnclosure.PowerCertificate :=
    ⟨2, 1278467/2000000, 14, 189502/100000, 19/10⟩
  have hc : cert.check (1278467/1000000) (1000000/278467) 4 = true := by decide +kernel
  have hexp := (cert.check_sound hc).1
  norm_num at hexp
  have hcap : (1:ℝ) ≤ (278467/1000000)*Real.exp (1+278467/1000000) := by
    norm_num only [show (1+278467/1000000:ℝ) = 1278467/1000000 by norm_num]
    nlinarith
  have h := source_capacity_reciprocal_lower (b:=1) (K:=278467/1000000)
    (by norm_num) (by norm_num) hp (by norm_num; exact hpq) hcap
  norm_num at h ⊢
  exact h

private theorem log_thirty_one_bounds : (2:ℝ) ≤ Real.log 31 ∧ Real.log 31 ≤ 4 := by
  have hc : ExpEnclosure.smallCheck 1 10 (5/2) 3 = true := by decide +kernel
  have he := ExpEnclosure.smallCheck_sound hc
  norm_num at he
  constructor
  · apply Real.exp_le_exp.mp
    rw [Real.exp_log (by norm_num : (0:ℝ)<31)]
    have hsq := pow_le_pow_left₀ (Real.exp_pos 1).le he.2 2
    have htwo := ExpEnclosure.exp_nat_mul 1 2
    norm_num only [Nat.cast_ofNat, mul_one] at htwo
    nlinarith
  · apply Real.exp_le_exp.mp
    rw [Real.exp_log (by norm_num : (0:ℝ)<31)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5/2) he.1 4
    have hfour := ExpEnclosure.exp_nat_mul 1 4
    norm_num only [Nat.cast_ofNat, mul_one] at hfour
    nlinarith

/-- A real interval reaching all the way to zero is bounded analytically;
there is no smallest positive probability or grid truncation. -/
theorem source_case_one_origin_capacity {p : ℝ} (hp : 0 < p) (hph : p ≤ 1/32) :
    (8:ℝ) ≤ 1/(p*sourceLogCapacity 1 p) := by
  have hr : 0 < (1-p)/p := div_pos (by linarith) hp
  have hl := Real.log_le_sub_one_of_pos (div_pos hr (by norm_num : (0:ℝ)<31))
  rw [Real.log_div hr.ne' (by norm_num)] at hl
  have hmul := mul_le_mul_of_nonneg_left hl hp.le
  have he : p*((1-p)/p/31-1) = (1-p)/31-p := by field_simp
  rw [he] at hmul
  have hL := log_thirty_one_bounds
  have hmono := mul_le_mul_of_nonneg_right hph
    (show 0 ≤ Real.log (31:ℝ)-32/31 by linarith)
  have hcap : p*sourceLogCapacity 1 p ≤ 1/8 := by
    simp only [sourceLogCapacity, one_mul]
    nlinarith
  have hpos := source_log_capacity_pos (b:=1) (by norm_num) hp (by norm_num; linarith)
  apply (le_div_iff₀ (mul_pos hp hpos)).mpr
  nlinarith

/-- Exact integer-piece formula. The witnesses are rational power comparisons;
no floor of an approximate logarithm is trusted. -/
theorem sourceOddsCapacity_one_log_pow {x : ℝ} (j : ℕ)
    (hxlo : (2:ℝ)^j ≤ x) (hxhi : x < (2:ℝ)^(j+1)) :
    sourceOddsCapacity 1 (Real.log x) = (j:ℝ)+x/2^j-1 := by
  have hx : 0 < x := (pow_pos (by norm_num : (0:ℝ)<2) j).trans_le hxlo
  have hL : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg ((one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hxlo)
  have hf : Nat.floor (Real.log x / Real.log (2:ℝ)) = j := by
    apply (Nat.floor_eq_iff (div_nonneg hlog hL.le)).mpr
    constructor
    · apply (le_div_iff₀ hL).mpr
      have h := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) j) hxlo
      simpa only [Real.log_pow] using h
    · apply (div_lt_iff₀ hL).mpr
      have h := Real.log_lt_log hx hxhi
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h
  have hexp : Real.exp (Real.log x-(j:ℝ)*Real.log 2) = x/2^j := by
    rw [← Real.log_pow, Real.exp_sub, Real.exp_log hx,
      Real.exp_log (pow_pos (by norm_num : (0:ℝ)<2) j)]
  simp only [sourceOddsCapacity, one_add_one_eq_two, hf, hexp, mul_one]

theorem sourceOddsCapacity_pos {b T : ℝ} (hb : 0 < b) (hT : 0 < T) :
    0 < sourceOddsCapacity b T := by
  by_cases hj : Nat.floor (T/Real.log (1+b)) = 0
  · simp only [sourceOddsCapacity, hj, Nat.cast_zero, zero_mul, sub_zero, zero_add]
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hT)
  · have hn : (0:ℝ) < (Nat.floor (T/Real.log (1+b)) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hj
    exact (mul_pos hn hb).trans_le (sourceOddsCapacity_bounds hb hT.le).1

/-- Coarse but convergent interval capacity bounds. Refining a probability
cell approaches the exact capacities at every interior point. -/
theorem source_cell_capacity_bounds {pl ph p tUpper L H : ℝ} (j : ℕ)
    (hpl : 0 < pl) (hplp : pl ≤ p) (hpph : p ≤ ph) (hpq : p < 1/2)
    (hlog : Real.log ((1-pl)/pl) ≤ tUpper)
    (hL : L ≤ 1000000/278467 ∨ L*(ph*tUpper) ≤ 1) (hL0 : 0 ≤ L)
    (hjlo : (2:ℝ)^j ≤ (1-pl)/pl) (hjhi : (1-pl)/pl < (2:ℝ)^(j+1))
    (hH : H*((j:ℝ)+((1-pl)/pl)/2^j-1) ≤ 1) :
    L ≤ 1/(p*sourceLogCapacity 1 p) ∧
      H ≤ 1/sourceOddsCapacity 1 (sourceLogCapacity 1 p) := by
  have hp : 0 < p := hpl.trans_le hplp
  have hplq : pl < 1/2 := hplp.trans_lt hpq
  have hratio : (1-p)/p ≤ (1-pl)/pl := by
    apply (div_le_div_iff₀ hp hpl).mpr
    nlinarith
  have hratioPos : 0 < (1-p)/p := div_pos (by linarith) hp
  have hTpos := source_log_capacity_pos (b:=1) (by norm_num) hp (by norm_num; exact hpq)
  have hTle : sourceLogCapacity 1 p ≤ Real.log ((1-pl)/pl) := by
    simp only [sourceLogCapacity, one_mul]
    exact Real.log_le_log hratioPos hratio
  constructor
  · rcases hL with hL | hL
    · exact hL.trans (source_case_one_global_capacity hp hpq)
    · apply (le_div_iff₀ (mul_pos hp hTpos)).mpr
      have hprod := mul_le_mul hpph (hTle.trans hlog) hTpos.le (hp.le.trans hpph)
      exact (mul_le_mul_of_nonneg_left hprod hL0).trans hL
  · have hHpos := sourceOddsCapacity_pos (by norm_num : (0:ℝ)<1) hTpos
    have hHle := sourceOddsCapacity_mono (by norm_num : (0:ℝ)<1) hTpos.le hTle
    rw [sourceOddsCapacity_one_log_pow j hjlo hjhi] at hHle
    have hHLpos : 0 < (j:ℝ)+((1-pl)/pl)/2^j-1 := hHpos.trans_le hHle
    exact ((le_div_iff₀ hHLpos).mpr hH).trans (one_div_le_one_div_of_le hHpos hHle)

/-- The log contribution is bounded according to the sign of its rational
numerator; negative numerators use the left endpoint denominator. -/
theorem source_cell_log_bonus {pl ph p up low lowerLow B : ℝ}
    (hpl : 0 < pl) (hplp : pl ≤ p) (hpph : p ≤ ph) (hph1 : ph < 1)
    (hu : Real.log ph ≤ up) (hl : low ≤ Real.log (1-ph))
    (hLower : lowerLow ≤ Real.log (22/25:ℝ))
    (hB : B ≤ (-(240111/2000000)*(up-2*low-lowerLow)) /
      (if 0 ≤ -(240111/2000000)*(up-2*low-lowerLow) then ph else pl)) :
    B ≤ -(240111/2000000)*
      (Real.log p-2*Real.log (1-p)-Real.log (22/25:ℝ))/p := by
  have hp : 0 < p := hpl.trans_le hplp
  have hph : 0 < ph := hp.trans_le hpph
  have hlogp := (Real.log_le_log hp hpph).trans hu
  have hlogc := hl.trans (Real.log_le_log (sub_pos.mpr hph1) (by linarith : 1-ph ≤ 1-p))
  let N := -(240111/2000000:ℝ)*(up-2*low-lowerLow)
  have hN : N ≤ -(240111/2000000)*
      (Real.log p-2*Real.log (1-p)-Real.log (22/25:ℝ)) := by dsimp [N]; linarith
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

#print axioms source_cell_capacity_bounds
#print axioms source_cell_log_bonus
#print axioms source_case_one_origin_capacity
#print axioms source_probability_log_capacity_le
#print axioms source_case_one_global_capacity
end ForestUnimodality




