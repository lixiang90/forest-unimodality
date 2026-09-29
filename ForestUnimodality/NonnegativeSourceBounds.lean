import ForestUnimodality.NonnegativeSourceCertificate

/-! Real-domain bounds and complete response inequalities used to check
arbitrary nonnegative-source parameters by exact rational arithmetic. -/
namespace ForestUnimodality

theorem nonnegativeSourceEta_nonneg {b p : ℝ} (hb : 0<b) (hp : 0<p)
    (hpq : p<b/(1+b)) : 0≤nonnegativeSourceEta b p := by
  have hp1 : p<1 := hpq.trans ((div_lt_one (by linarith : 0<1+b)).mpr (by linarith))
  have hden : 0<1+b*(1-p) := by nlinarith [mul_pos hb (sub_pos.mpr hp1)]
  exact one_div_nonneg.mpr (mul_nonneg hden.le
    (sourceOddsCapacity_pos hb (source_log_capacity_pos hb hp hpq)).le)

theorem nonnegativeSourceEta_mono {b l p : ℝ} (hb : 0<b) (hl : 0<l)
    (hlp : l≤p) (hpq : p<b/(1+b)) : nonnegativeSourceEta b l≤nonnegativeSourceEta b p := by
  have hp := hl.trans_le hlp
  have hp1 : p<1 := hpq.trans ((div_lt_one (by linarith : 0<1+b)).mpr (by linarith))
  have hl1 := hlp.trans_lt hp1
  have hTp := source_log_capacity_pos hb hp hpq
  have hTl := source_log_capacity_pos hb hl (hlp.trans_lt hpq)
  have hlog : sourceLogCapacity b p≤sourceLogCapacity b l := by
    apply Real.log_le_log (div_pos (mul_pos hb (sub_pos.mpr hp1)) hp)
    apply (div_le_div_iff₀ hp hl).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hlp)]
  have hH := sourceOddsCapacity_mono hb hTp.le hlog
  have hHp := sourceOddsCapacity_pos hb hTp
  have hHl := sourceOddsCapacity_pos hb hTl
  have hden : 0<1+b*(1-p) := by nlinarith [mul_pos hb (sub_pos.mpr hp1)]
  apply one_div_le_one_div_of_le (mul_pos hden hHp)
  exact mul_le_mul (by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hlp)]) hH hHp.le
    (by nlinarith [mul_pos hb (sub_pos.mpr hl1)] : 0≤1+b*(1-l))

theorem nonnegativeSourceEta_log_piece {b p : ℝ} (hb : 0<b) (j : ℕ)
    (hjlo : (1+b)^j≤b*(1-p)/p) (hjhi : b*(1-p)/p<(1+b)^(j+1)) :
    nonnegativeSourceEta b p =
      1/((1+b*(1-p))*((j:ℝ)*b+(b*(1-p)/p)/(1+b)^j-1)) := by
  unfold nonnegativeSourceEta sourceLogCapacity
  rw [sourceOddsCapacity_log_pow hb j hjlo hjhi]

noncomputable def nonnegativeSourceEnvelope (mass E L dd hh u v z : ℝ) : ℝ :=
  mass+E*(1-z)^2-dd*z^2+
  u*(L*(max 0 (1-z))^2-hh*(max 0 z)^2)+
  v*(L*(max 0 (z-1))^2-hh*(max 0 (-z))^2)

/-- The four coefficient inequalities cover all three response regions.
The positive ray uses its full discriminant, not finitely many samples. -/
theorem nonnegativeSourceEnvelope_nonneg {mass E L dd hh u v : ℝ}
    (hm : 0≤mass) (hE : 0≤E) (hL : 0≤L) (hdd : 0≤dd) (hhh : 0≤hh)
    (hu : 0≤u) (_hv : 0≤v)
    (hnegative : 0≤E+u*L-(dd+v*hh))
    (hconstant : 0≤mass-(dd+u*hh))
    (hpositive : 0<E+v*L-(dd+u*hh))
    (hdisc : (dd+u*hh)^2≤(mass-(dd+u*hh))*(E+v*L-(dd+u*hh))) (z : ℝ) :
    0≤nonnegativeSourceEnvelope mass E L dd hh u v z := by
  have hA : 0≤E+u*L := add_nonneg hE (mul_nonneg hu hL)
  have hB : 0≤dd+u*hh := add_nonneg hdd (mul_nonneg hu hhh)
  by_cases hz : z≤0
  · have hn : 0≤-z := by linarith
    have h1z : 0≤1-z := by linarith
    have hz1 : z-1≤0 := by linarith
    have he : nonnegativeSourceEnvelope mass E L dd hh u v z =
        mass+(E+u*L)+2*(E+u*L)*(-z)+(E+u*L-(dd+v*hh))*(-z)^2 := by
      simp only [nonnegativeSourceEnvelope, max_eq_left hz, max_eq_right hn,
        max_eq_right h1z, max_eq_left hz1]
      ring
    rw [he]
    positivity
  · have hz0 : 0≤z := (lt_of_not_ge hz).le
    have hn : -z≤0 := by linarith
    by_cases hz1 : z≤1
    · have h1z : 0≤1-z := by linarith
      have hzm : z-1≤0 := by linarith
      have he : nonnegativeSourceEnvelope mass E L dd hh u v z =
          mass+(E+u*L)*(1-z)^2-(dd+u*hh)*z^2 := by
        simp only [nonnegativeSourceEnvelope, max_eq_right hz0, max_eq_left hn,
          max_eq_right h1z, max_eq_left hzm]
        ring
      rw [he]
      have hzsq : z^2≤1 := by nlinarith
      nlinarith [mul_nonneg hA (sq_nonneg (1-z)), mul_nonneg hB (sub_nonneg.mpr hzsq)]
    · have ht : 0≤z-1 := by linarith
      have h1z : 1-z≤0 := by linarith
      have he : nonnegativeSourceEnvelope mass E L dd hh u v z =
          (mass-(dd+u*hh))-2*(dd+u*hh)*(z-1)+(E+v*L-(dd+u*hh))*(z-1)^2 := by
        simp only [nonnegativeSourceEnvelope, max_eq_right hz0, max_eq_left hn,
          max_eq_left h1z, max_eq_right ht]
        ring
      rw [he]
      have hs := sq_nonneg ((E+v*L-(dd+u*hh))*(z-1)-(dd+u*hh))
      nlinarith

theorem nonnegativeSourceEnvelope_le {b A u v p ph E L dd hh z : ℝ}
    (hp : 0<p) (hpph : p≤ph) (hA : 0≤A) (hu : 0≤u) (hv : 0≤v)
    (hE : E≤nonnegativeSourceEta b p) (hL : L≤1/(p*sourceLogCapacity b p))
    (hdd : 1-p≤dd) (hhh : 1-p/2≤hh) :
    nonnegativeSourceEnvelope (A/ph) E L dd hh u v z ≤
      nonnegativeSourceHomogeneous b A u v p 1 z := by
  have hm := div_le_div_of_nonneg_left hA hp hpph
  have he := mul_le_mul_of_nonneg_right hE (sq_nonneg (1-z))
  have hd := mul_le_mul_of_nonneg_right hdd (sq_nonneg z)
  have hu1 := mul_le_mul_of_nonneg_right hL (sq_nonneg (max 0 (1-z)))
  have hu2 := mul_le_mul_of_nonneg_right hhh (sq_nonneg (max 0 z))
  have hv1 := mul_le_mul_of_nonneg_right hL (sq_nonneg (max 0 (z-1)))
  have hv2 := mul_le_mul_of_nonneg_right hhh (sq_nonneg (max 0 (-z)))
  have hup := mul_le_mul_of_nonneg_left (sub_le_sub hu1 hu2) hu
  have hvp := mul_le_mul_of_nonneg_left (sub_le_sub hv1 hv2) hv
  unfold nonnegativeSourceEnvelope nonnegativeSourceHomogeneous
  norm_num only [one_pow, mul_one]
  linarith

#print axioms nonnegativeSourceEta_mono
#print axioms nonnegativeSourceEnvelope_nonneg
#print axioms nonnegativeSourceEnvelope_le
end ForestUnimodality
