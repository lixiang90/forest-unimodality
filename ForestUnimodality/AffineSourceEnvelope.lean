import ForestUnimodality.AffineSourceCertificate
import ForestUnimodality.SelectionSourceBounds

namespace ForestUnimodality.AffineSource
open PolynomialList BernsteinCertificate ParametricQuadratic

structure Parameters where
  A : ℚ
  C : ℚ
  u : ℚ
  v : ℚ
  s : ℚ

noncomputable def Parameters.toReal (P : Parameters) : AffineSourceParameters :=
  ⟨P.A,P.C,P.u,P.v,P.s⟩

def Parameters.check (P : Parameters) : Bool :=
  decide (0≤P.A ∧ 0≤P.C ∧ 0≤P.u ∧ 0≤P.v ∧ 0≤P.s)

theorem Parameters.check_sound {P : Parameters} (hc : P.check=true) :
    P.toReal.Admissible ∧ 0≤P.toReal.A ∧ 0≤P.toReal.C := by
  have h : 0≤P.A ∧ 0≤P.C ∧ 0≤P.u ∧ 0≤P.v ∧ 0≤P.s := of_decide_eq_true hc
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩ <;> dsimp only [Parameters.toReal]
  · exact_mod_cast h.2.2.1
  · exact_mod_cast h.2.2.2.1
  · exact_mod_cast h.2.2.2.2
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1

def Parameters.selection (P : Parameters) : SelectionSource.Parameters :=
  ⟨0,P.C,P.u,P.v,0,0,P.s⟩

structure Bounds where
  mass : ℚ
  L : ℚ
  H : ℚ
  hh : ℚ
  dd : ℚ

def Bounds.selection (d : Bounds) : SelectionSource.Bounds := ⟨d.L,d.H,d.hh,d.dd,0,0,0⟩

noncomputable def envelope (P : Parameters) (d : Bounds) (r z : ℝ) : ℝ :=
  d.mass+SelectionSource.envelope P.selection d.selection r z

def addMass (Q : Quad) (mass : ℚ) : Quad := ⟨Q.A,Q.B,Q.C+PolynomialList.C mass⟩

theorem addMass_value (Q : Quad) (mass : ℚ) (r z : ℝ) :
    (addMass Q mass).value r z = (mass:ℝ)+Q.value r z := by
  simp only [addMass,Quad.value,evalReal,eval_add,eval_C]
  norm_num only [rationalEvaluation]
  ring

def negativeQuad (P : Parameters) (d : Bounds) : Quad :=
  addMass (SelectionSource.negativeQuad P.selection d.selection) d.mass
def middleQuad (P : Parameters) (d : Bounds) : Quad :=
  addMass (SelectionSource.middleQuad P.selection d.selection) d.mass
def positiveQuad (P : Parameters) (d : Bounds) : Quad :=
  addMass (SelectionSource.positiveQuad P.selection d.selection) d.mass

theorem negativeQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ) (hx : 0≤x) :
    envelope P d r (-x)=(negativeQuad P d).value r x := by
  rw [negativeQuad,addMass_value,envelope,SelectionSource.negativeQuad_identity _ _ _ _ hx]

theorem middleQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) :
    envelope P d r (1-x)=(middleQuad P d).value r x := by
  rw [middleQuad,addMass_value,envelope,SelectionSource.middleQuad_identity _ _ _ _ hx]

theorem positiveQuad_identity (P : Parameters) (d : Bounds) (r x : ℝ) (hx : 0≤x) :
    envelope P d r (1+x)=(positiveQuad P d).value r x := by
  rw [positiveQuad,addMass_value,envelope,SelectionSource.positiveQuad_identity _ _ _ _ hx]

abbrev EnvelopeCertificate := SelectionSource.EnvelopeCertificate

def envelopeCheck (c : EnvelopeCertificate) (P : Parameters) (d : Bounds) : Bool :=
  c.negative.check (negativeQuad P d) c.lo c.hi &&
  c.middle.check (middleQuad P d) c.lo c.hi &&
  c.positive.check (positiveQuad P d) c.lo c.hi

theorem envelopeCheck_sound {c : EnvelopeCertificate} {P : Parameters} {d : Bounds}
    (hc : envelopeCheck c P d=true) {r z : ℝ} (hr : r∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    0≤envelope P d r z := by
  have h : c.negative.check (negativeQuad P d) c.lo c.hi=true ∧
      c.middle.check (middleQuad P d) c.lo c.hi=true ∧
      c.positive.check (positiveQuad P d) c.lo c.hi=true := by
    simpa only [envelopeCheck,Bool.and_eq_true_iff,and_assoc] using hc
  by_cases hz : z≤0
  · have hn := c.negative.check_sound h.1 hr (neg_nonneg.mpr hz)
    rw [←negativeQuad_identity P d r (-z) (neg_nonneg.mpr hz),neg_neg] at hn
    exact hn
  · have hz0 : 0≤z := (lt_of_not_ge hz).le
    by_cases hz1 : z≤1
    · have hx : 1-z∈Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hz1,by linarith⟩
      have hm := c.middle.check_sound h.2.1 hr hx
      rw [←middleQuad_identity P d r (1-z) hx] at hm
      simpa only [sub_sub_cancel] using hm
    · have hx : 0≤z-1 := by linarith
      have hp := c.positive.check_sound h.2.2 hr hx
      rw [←positiveQuad_identity P d r (z-1) hx] at hp
      convert hp using 1
      congr 1
      ring

theorem envelope_le (P : Parameters) (d : Bounds) (hP : P.check=true)
    {b p r z : ℝ} (hb : 0<b) (hp : 0<p) (hr0 : 0≤r) (hr1 : r≤1)
    (hmass : (d.mass:ℝ)≤(P.A:ℝ)/p)
    (hcap : (d.L:ℝ)≤1/(p*sourceLogCapacity b p) ∧
      (d.H:ℝ)≤1/sourceOddsCapacity b (sourceLogCapacity b p))
    (hhh : 1-p/2≤(d.hh:ℝ)) (hdd : 1-p≤(d.dd:ℝ)) :
    envelope P d r z≤affineSourceRow P.toReal b p r 1 z := by
  have hsign := Parameters.check_sound hP
  have hsel : P.selection.toReal.Admissible :=
    ⟨hsign.1.1,hsign.1.2.1,by simp [Parameters.selection,SelectionSource.Parameters.toReal],hsign.1.2.2⟩
  have hphi : (0:ℝ)≤sourcePhi 1 b p := by
    unfold sourcePhi
    apply mul_nonneg
    · exact div_nonneg (div_nonneg hb.le (by linarith)) (Real.log_pos (by linarith)).le
    · exact le_max_left _ _
  have hf : (0:ℝ)≤MarginalSelectionBound.selectionFraction (b/(1+b)) (p*r) := by
    have ht := SelectionSource.selectionFraction_first_lower (q:=b/(1+b)) (pl:=0)
      (p:=p) (r:=r) (by positivity) hp.le hr0
    simpa only [mul_zero,zero_mul] using ht
  have hs := SelectionSource.envelope_le P.selection d.selection hsel (z:=z)
    (by simp [Parameters.selection,SelectionSource.Parameters.toReal]) hr0 hr1 hcap
    (by simpa only [Bounds.selection,Rat.cast_zero] using hphi) hhh hdd
    (by simpa only [Bounds.selection,Rat.cast_zero,zero_mul,zero_add] using hf)
  have hadd := add_le_add hmass hs
  calc
    envelope P d r z ≤ (P.A:ℝ)/p+sourceSelectionScalarRow P.selection.toReal 1 b p r z := hadd
    _ = affineSourceRow P.toReal b p r 1 z := by
      simp only [affineSourceRow,Parameters.toReal,sourceSelectionScalarRow,Parameters.selection,
        SelectionSource.Parameters.toReal,one_pow,Rat.cast_zero,zero_mul,zero_add,add_zero]
      ring

#print axioms envelopeCheck_sound
#print axioms envelope_le
end ForestUnimodality.AffineSource
