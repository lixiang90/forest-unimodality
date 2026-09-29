import ForestUnimodality.SourceScalarCaseOne

/-! Rational quadratic certificates for an entire response/retention
envelope. The transcendental source-to-envelope bound is checked separately. -/
namespace ForestUnimodality

structure SourceEnvelopeBounds where
  L : ℚ
  H : ℚ
  hh : ℚ
  dd : ℚ
  B : ℚ
  rl : ℚ
  rh : ℚ

noncomputable def sourceEnvelope (L H hh dd B a parentA r z : ℝ) : ℝ :=
  let P := sourceParameters_22_25_1
  r*(P.A+P.C*a)-r*dd*z^2+B +
    P.positivePrice a*L*(max 0 (a-z))^2-P.positivePrice parentA*hh*(max 0 z)^2 +
    P.negativePrice a*L*(max 0 (z-a))^2-P.negativePrice parentA*hh*(max 0 (-z))^2 +
    P.responsePrice*(z-r*a)+P.blockingPrice*(r*(a-z)^2*H-(1-r)*dd*z^2)

namespace SourceEnvelopeCertificate
def posPrice (a : ℚ) : ℚ := if a=1 then 10854739/50000000 else 1729251/5000000
def negPrice (a : ℚ) : ℚ := if a=1 then 11742489/25000000 else 24188011/100000000

theorem posPrice_cast (a : ℚ) : (posPrice a : ℝ) = sourceParameters_22_25_1.positivePrice a := by
  by_cases h : a=1
  · simp [posPrice, h, sourceParameters_22_25_1]
  · have hr : (a : ℝ) ≠ 1 := by exact_mod_cast h
    simp [posPrice, h, sourceParameters_22_25_1, hr]

theorem negPrice_cast (a : ℚ) : (negPrice a : ℝ) = sourceParameters_22_25_1.negativePrice a := by
  by_cases h : a=1
  · simp [negPrice, h, sourceParameters_22_25_1]
  · have hr : (a : ℝ) ≠ 1 := by exact_mod_cast h
    simp [negPrice, h, sourceParameters_22_25_1, hr]

structure Quad where
  A : ℚ
  B : ℚ
  C : ℚ

def Quad.rayCheck (p : Quad) : Bool := QuadraticCertificate.rayCheck p.A p.B p.C 0
def Quad.unitCheck (p : Quad) : Bool := decide (0 ≤ p.C ∧ 0 ≤ p.A+p.B+p.C ∧
  (p.A ≤ 0 ∨ 0 ≤ p.B ∨ p.B ≤ -2*p.A ∨ p.B^2 ≤ 4*p.A*p.C))

theorem Quad.rayCheck_sound {p : Quad} (h : p.rayCheck=true) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (p.A : ℝ)*x^2+(p.B : ℝ)*x+p.C := by
  have hp := QuadraticCertificate.rayCheck_sound h (x := x) (by simpa using hx)
  simpa only [QuadraticCertificate.evalReal_quadratic] using hp

theorem Quad.unitCheck_sound {p : Quad} (h : p.unitCheck=true) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ (p.A : ℝ)*x^2+(p.B : ℝ)*x+p.C := by
  have hq : 0 ≤ p.C ∧ 0 ≤ p.A+p.B+p.C ∧
      (p.A ≤ 0 ∨ 0 ≤ p.B ∨ p.B ≤ -2*p.A ∨ p.B^2 ≤ 4*p.A*p.C) := of_decide_eq_true h
  have hr : (0 : ℝ) ≤ p.C ∧ 0 ≤ (p.A : ℝ)+p.B+p.C ∧
      ((p.A : ℝ) ≤ 0 ∨ 0 ≤ (p.B : ℝ) ∨ (p.B : ℝ) ≤ -2*(p.A : ℝ) ∨
        (p.B : ℝ)^2 ≤ 4*(p.A : ℝ)*p.C) := by exact_mod_cast hq
  rcases hr.2.2 with ha | hb | hb | hd
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
      mul_nonneg (neg_nonneg.mpr ha) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
      mul_nonneg hx.1 hr.2.1, mul_nonneg (sub_nonneg.mpr hx.2) hr.1]
  · by_cases ha : 0 ≤ (p.A : ℝ)
    · exact add_nonneg (add_nonneg (mul_nonneg ha (sq_nonneg x)) (mul_nonneg hb hx.1)) hr.1
    · have hh : (p.A : ℝ) ≤ 0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 hr.2.1, mul_nonneg (sub_nonneg.mpr hx.2) hr.1]
  · by_cases ha : 0 ≤ (p.A : ℝ)
    · have hdiff : 0 ≤ (1-x)*(-(p.A : ℝ)*(1+x)-p.B) := by
        apply mul_nonneg (sub_nonneg.mpr hx.2)
        nlinarith [mul_le_mul_of_nonneg_left hx.2 ha]
      nlinarith
    · have hh : (p.A : ℝ) ≤ 0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 hr.2.1, mul_nonneg (sub_nonneg.mpr hx.2) hr.1]
  · by_cases ha : 0 ≤ (p.A : ℝ)
    · exact QuadraticCertificate.quadratic_nonneg_on_nonneg ha hr.1 (Or.inr hd) hx.1
    · have hh : (p.A : ℝ) ≤ 0 := le_of_not_ge ha
      nlinarith [mul_nonneg (neg_nonneg.mpr hh) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
        mul_nonneg hx.1 hr.2.1, mul_nonneg (sub_nonneg.mpr hx.2) hr.1]

def negativeQuad (d : SourceEnvelopeBounds) (a pa r : ℚ) : Quad where
  A := -r*d.dd+posPrice a*d.L-negPrice pa*d.hh+
    (89615257/100000000)*(r*d.H-(1-r)*d.dd)
  B := 2*a*posPrice a*d.L-96780649/100000000+2*a*(89615257/100000000)*r*d.H
  C := r*(14896533/50000000+(3577121/5000000)*a)+d.B-
    (96780649/100000000)*r*a+posPrice a*d.L*a^2+(89615257/100000000)*r*d.H*a^2

def positiveQuad (d : SourceEnvelopeBounds) (a pa r : ℚ) : Quad where
  A := -r*d.dd-posPrice pa*d.hh+negPrice a*d.L+
    (89615257/100000000)*(r*d.H-(1-r)*d.dd)
  B := -2*a*r*d.dd-2*a*posPrice pa*d.hh+96780649/100000000-
    2*a*(89615257/100000000)*(1-r)*d.dd
  C := r*(14896533/50000000+(3577121/5000000)*a)+d.B+
    (96780649/100000000)*(a-r*a)-a^2*r*d.dd-posPrice pa*d.hh*a^2-
    (89615257/100000000)*(1-r)*d.dd*a^2

def middleQuad (d : SourceEnvelopeBounds) (r : ℚ) : Quad where
  A := -r*d.dd+posPrice 1*d.L-posPrice 0*d.hh+
    (89615257/100000000)*(r*d.H-(1-r)*d.dd)
  B := 2*r*d.dd+2*posPrice 0*d.hh-96780649/100000000+
    2*(89615257/100000000)*(1-r)*d.dd
  C := (positiveQuad d 1 0 r).C

theorem negativeQuad_identity (d : SourceEnvelopeBounds) (a pa r : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    sourceEnvelope d.L d.H d.hh d.dd d.B a pa r (-x) =
      ((negativeQuad d a pa r).A : ℝ)*x^2+((negativeQuad d a pa r).B : ℝ)*x+
        (negativeQuad d a pa r).C := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : 0 ≤ (a : ℝ)+x := by linarith
  have han : -x-(a : ℝ) ≤ 0 := by linarith
  simp only [sourceEnvelope, neg_neg, sub_neg_eq_add, max_eq_right hap,
    max_eq_left (neg_nonpos.mpr hx), max_eq_left han, max_eq_right hx,
    negativeQuad]
  push_cast
  rw [posPrice_cast, negPrice_cast]
  simp only [sourceParameters_22_25_1]
  ring

theorem positiveQuad_identity (d : SourceEnvelopeBounds) (a pa r : ℚ) (x : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    sourceEnvelope d.L d.H d.hh d.dd d.B a pa r ((a : ℝ)+x) =
      ((positiveQuad d a pa r).A : ℝ)*x^2+((positiveQuad d a pa r).B : ℝ)*x+
        (positiveQuad d a pa r).C := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : 0 ≤ (a : ℝ)+x := by linarith
  have ha1 : (a : ℝ)-((a : ℝ)+x) = -x := by ring
  have ha2 : (a : ℝ)+x-(a : ℝ) = x := by ring
  simp only [sourceEnvelope, ha1, ha2, max_eq_left (neg_nonpos.mpr hx),
    max_eq_left (neg_nonpos.mpr hap), max_eq_right hx, max_eq_right hap, positiveQuad]
  push_cast
  rw [posPrice_cast, negPrice_cast]
  simp only [sourceParameters_22_25_1]
  ring

theorem middleQuad_identity (d : SourceEnvelopeBounds) (r : ℚ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    sourceEnvelope d.L d.H d.hh d.dd d.B 1 0 r (1-x) =
      ((middleQuad d r).A : ℝ)*x^2+((middleQuad d r).B : ℝ)*x+(middleQuad d r).C := by
  have h1 : 1-(1-x)=x := by ring
  have h2 : 1-x-1= -x := by ring
  simp only [sourceEnvelope, h1, h2, max_eq_left (neg_nonpos.mpr hx.1),
    max_eq_left (neg_nonpos.mpr (sub_nonneg.mpr hx.2)), max_eq_right hx.1,
    max_eq_right (sub_nonneg.mpr hx.2), middleQuad, positiveQuad]
  norm_num [posPrice, negPrice, sourceParameters_22_25_1]
  ring

def endpointCheck (d : SourceEnvelopeBounds) (r : ℚ) : Bool :=
  (negativeQuad d 0 0 r).rayCheck && (positiveQuad d 0 0 r).rayCheck &&
  (negativeQuad d 0 1 r).rayCheck && (positiveQuad d 0 1 r).rayCheck &&
  (negativeQuad d 1 0 r).rayCheck && (positiveQuad d 1 0 r).rayCheck && (middleQuad d r).unitCheck

theorem endpointCheck_sound {d : SourceEnvelopeBounds} {r : ℚ} (h : endpointCheck d r=true)
    {a pa : ℝ} (hs : SourceMarkState a pa) (z : ℝ) :
    0 ≤ sourceEnvelope d.L d.H d.hh d.dd d.B a pa r z := by
  have he : (negativeQuad d 0 0 r).rayCheck=true ∧ (positiveQuad d 0 0 r).rayCheck=true ∧
      (negativeQuad d 0 1 r).rayCheck=true ∧ (positiveQuad d 0 1 r).rayCheck=true ∧
      (negativeQuad d 1 0 r).rayCheck=true ∧ (positiveQuad d 1 0 r).rayCheck=true ∧
      (middleQuad d r).unitCheck=true := by
    simpa only [endpointCheck, Bool.and_eq_true_iff, and_assoc] using h
  rcases he with ⟨hn00,hp00,hn01,hp01,hn10,hp10,hm⟩
  have hneg (a pa : ℚ) (ha : 0 ≤ a) (hh : (negativeQuad d a pa r).rayCheck=true)
      (hz : z ≤ 0) : 0 ≤ sourceEnvelope d.L d.H d.hh d.dd d.B a pa r z := by
    have hx : 0 ≤ -z := by linarith
    have hq := Quad.rayCheck_sound hh hx
    rw [← negativeQuad_identity d a pa r (-z) ha hx, neg_neg] at hq
    exact hq
  have hpos (a pa : ℚ) (ha : 0 ≤ a) (hh : (positiveQuad d a pa r).rayCheck=true)
      (hz : (a : ℝ) ≤ z) : 0 ≤ sourceEnvelope d.L d.H d.hh d.dd d.B a pa r z := by
    have hx : 0 ≤ z-(a : ℝ) := sub_nonneg.mpr hz
    have hq := Quad.rayCheck_sound hh hx
    rw [← positiveQuad_identity d a pa r (z-a) ha hx] at hq
    have he : (a : ℝ)+(z-a)=z := by ring
    rwa [he] at hq
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero] using hneg 0 0 (by norm_num) hn00 hz
    · simpa only [Rat.cast_zero] using hpos 0 0 (by norm_num) hp00 (by simpa using (le_of_not_ge hz))
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero, Rat.cast_one] using hneg 0 1 (by norm_num) hn01 hz
    · simpa only [Rat.cast_zero, Rat.cast_one] using hpos 0 1 (by norm_num) hp01 (by simpa using (le_of_not_ge hz))
  · by_cases hz : z ≤ 0
    · simpa only [Rat.cast_zero, Rat.cast_one] using hneg 1 0 (by norm_num) hn10 hz
    · by_cases hz1 : 1 ≤ z
      · simpa only [Rat.cast_zero, Rat.cast_one] using hpos 1 0 (by norm_num) hp10 (by simpa using hz1)
      · have hx : 1-z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
        have hq := Quad.unitCheck_sound hm hx
        rw [← middleQuad_identity d r hx] at hq
        have he : 1-(1-z)=z := by ring
        rwa [he] at hq
end SourceEnvelopeCertificate

def SourceEnvelopeBounds.check (d : SourceEnvelopeBounds) : Bool :=
  SourceEnvelopeCertificate.endpointCheck d d.rl && SourceEnvelopeCertificate.endpointCheck d d.rh

theorem SourceEnvelopeBounds.check_sound {d : SourceEnvelopeBounds} (h : d.check=true)
    {a parentA r z : ℝ} (hs : SourceMarkState a parentA)
    (hr : (d.rl : ℝ) ≤ r) (hrh : r ≤ (d.rh : ℝ)) :
    0 ≤ sourceEnvelope d.L d.H d.hh d.dd d.B a parentA r z := by
  have hh : SourceEnvelopeCertificate.endpointCheck d d.rl=true ∧
      SourceEnvelopeCertificate.endpointCheck d d.rh=true := by
    simpa only [SourceEnvelopeBounds.check, Bool.and_eq_true_iff] using h
  have hlo := SourceEnvelopeCertificate.endpointCheck_sound hh.1 hs z
  have hhi := SourceEnvelopeCertificate.endpointCheck_sound hh.2 hs z
  by_cases he : (d.rl : ℝ) = d.rh
  · have hr' : r=(d.rl : ℝ) := by linarith
    rwa [hr']
  · have hpos : 0 < (d.rh : ℝ)-d.rl :=
      sub_pos.mpr (lt_of_le_of_ne (hr.trans hrh) he)
    have hid : sourceEnvelope d.L d.H d.hh d.dd d.B a parentA r z =
        (((d.rh : ℝ)-r)/((d.rh : ℝ)-d.rl))*sourceEnvelope d.L d.H d.hh d.dd d.B a parentA d.rl z +
        ((r-(d.rl : ℝ))/((d.rh : ℝ)-d.rl))*sourceEnvelope d.L d.H d.hh d.dd d.B a parentA d.rh z := by
      unfold sourceEnvelope
      field_simp
      ring
    rw [hid]
    exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hrh) hpos.le) hlo)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hr) hpos.le) hhi)

#print axioms SourceEnvelopeBounds.check_sound
end ForestUnimodality
