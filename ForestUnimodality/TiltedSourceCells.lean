import ForestUnimodality.TiltedSourceEnvelope
import ForestUnimodality.MessageSourceCellBounds

/-! Continuous certificates for each of the three legal independent-mark
states. Source and parent activities may have different upper bounds. -/
namespace ForestUnimodality.TiltedSource
open SelectionSource

structure Cell where
  base : SelectionSource.Cell

def Cell.left (c : Cell) : ℚ := c.base.left
def Cell.right (c : Cell) : ℚ := c.base.right

def Cell.bounds (c : Cell) (parentCap : ℚ) : Bounds :=
  ⟨c.base.L,1-c.base.left/2,1-c.base.left,
    1/(1+parentCap*(1-c.base.left)),1⟩

def Cell.Accepts (c : Cell) (P : Parameters) (s : Fin 3)
    (D : Domain) (parentCap : ℚ) : Prop :=
  0≤c.left ∧ c.left<c.right ∧ c.right≤probabilityCap D ∧
  0≤c.base.L ∧ 0<parentCap ∧ c.base.CapacityAccepts D ∧
  (c.bounds parentCap).check P s=true

instance (c : Cell) (P : Parameters) (s : Fin 3) (D : Domain) (b : ℚ) :
    Decidable (c.Accepts P s D b) := by
  unfold Cell.Accepts SelectionSource.Cell.CapacityAccepts
  infer_instance

def Cell.check (c : Cell) (P : Parameters) (s : Fin 3)
    (D : Domain) (parentCap : ℚ) : Bool := decide (c.Accepts P s D parentCap)

theorem Cell.check_sound {c : Cell} {P : Parameters} {s : Fin 3}
    {D : Domain} {parentCap : ℚ} (cap : ℝ→ℝ)
    (hc : c.check P s D parentCap=true) (hD : D.Valid) (hP : P.check=true)
    (hcap : cap (sourceMark s)=(D.b:ℝ))
    {p r z : ℝ} (hp : 0<p) (hlp : (c.left:ℝ)≤p) (hpr : p≤(c.right:ℝ))
    (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ)))
    (hr : 1/(1+(parentCap:ℝ)*(1-p))≤r) (hr1 : r≤1) :
    0≤tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s) p r z := by
  have hh : c.Accepts P s D parentCap := of_decide_eq_true hc
  rcases hh with ⟨hl,_,_,hL,hb,hcapacity,hcheck⟩
  have hbR : (0:ℝ)<parentCap := by exact_mod_cast hb
  have hq1 : (D.b:ℝ)/(1+(D.b:ℝ))<1 :=
    (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hp1 := hpq.trans hq1
  have hd : 0<1+(parentCap:ℝ)*(1-p) := by
    nlinarith [mul_pos hbR (sub_pos.mpr hp1)]
  have hr0 : 0≤r := (div_nonneg (by norm_num) hd.le).trans hr
  have hret : ((c.bounds parentCap).rl:ℝ)≤r := by
    simp only [Cell.bounds,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
    apply le_trans ?_ hr
    apply one_div_le_one_div_of_le hd
    have hmul := mul_le_mul_of_nonneg_left hlp hbR.le
    change (c.base.left:ℝ)≤p at hlp
    change (parentCap:ℝ)*(c.base.left:ℝ)≤(parentCap:ℝ)*p at hmul
    linarith
  have hcapacities := c.base.capacity_bounds hD hcapacity
    (by exact_mod_cast hl : (0:ℝ)≤c.base.left) (by exact_mod_cast hL)
    hp hlp hpr hpq
  apply (Bounds.check_sound hcheck hret (by simpa only [Cell.bounds,Rat.cast_one] using hr1)).trans
  apply envelope_le P (c.bounds parentCap) hP cap hr0
  · simpa only [Cell.bounds,hcap] using hcapacities.1
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    change (c.base.left:ℝ)≤p at hlp
    linarith
  · simp only [Cell.bounds,Rat.cast_sub,Rat.cast_one]
    exact sub_le_sub_left hlp 1

def leafValue (P : Parameters) (s : Fin 3) (D : Domain) (r : ℚ) : ℚ :=
  P.C*r*sourceMark s-r*(1-probabilityCap D)*(sourceMark s)^2-
    (if parentMark s=1 then P.u1 else P.u0)*(1-probabilityCap D/2)*(sourceMark s)^2

def leafLower (D : Domain) (parentCap : ℚ) : ℚ :=
  1/(1+parentCap*(1-probabilityCap D))

def leafCheck (P : Parameters) (s : Fin 3) (D : Domain) (parentCap : ℚ) : Bool :=
  decide (0<parentCap ∧ 0≤leafValue P s D (leafLower D parentCap) ∧ 0≤leafValue P s D 1)

theorem leafValue_eq (P : Parameters) (s : Fin 3) (D : Domain)
    (r : ℚ) (cap : ℝ→ℝ) :
    (leafValue P s D r:ℝ)=
      tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s)
        (probabilityCap D) r (sourceMark s) := by
  fin_cases s <;>
    simp [leafValue,sourceMark,parentMark,tiltedSourceRow,Parameters.toReal,
      Parameters.source,RationalSourceParameters.toReal]

theorem leafCheck_sound {P : Parameters} {s : Fin 3} {D : Domain} {parentCap : ℚ}
    (cap : ℝ→ℝ) (hc : leafCheck P s D parentCap=true) (hD : D.Valid)
    {r : ℝ} (hr : 1/(1+(parentCap:ℝ)*(1-(probabilityCap D:ℝ)))≤r) (hr1 : r≤1) :
    0≤tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s)
      (probabilityCap D) r (sourceMark s) := by
  have h : 0<parentCap ∧ 0≤leafValue P s D (leafLower D parentCap) ∧
      0≤leafValue P s D 1 := of_decide_eq_true hc
  have hlo : (0:ℝ)≤leafValue P s D (leafLower D parentCap) := by exact_mod_cast h.2.1
  have hhi : (0:ℝ)≤leafValue P s D 1 := by exact_mod_cast h.2.2
  rw [leafValue_eq P s D (leafLower D parentCap) cap] at hlo
  rw [leafValue_eq P s D 1 cap] at hhi
  have hrl : (leafLower D parentCap:ℝ)≤r := by
    simpa only [leafLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub] using hr
  have hq1 : (probabilityCap D:ℝ)<1 := by
    simp only [probabilityCap,Rat.cast_div,Rat.cast_add,Rat.cast_one]
    exact (div_lt_one (by linarith [hD.b_pos])).mpr (by linarith)
  have hbR : (0:ℝ)<parentCap := by exact_mod_cast h.1
  have hrl1 : (leafLower D parentCap:ℝ)<1 := by
    simp only [leafLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub]
    have hmul := mul_pos hbR (sub_pos.mpr hq1)
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hid : tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s)
      (probabilityCap D) r (sourceMark s) =
      ((1-r)/(1-(leafLower D parentCap:ℝ)))*
        tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s)
          (probabilityCap D) (leafLower D parentCap) (sourceMark s)+
      ((r-(leafLower D parentCap:ℝ))/(1-(leafLower D parentCap:ℝ)))*
        tiltedSourceRow P.toReal cap (sourceMark s) (parentMark s)
          (probabilityCap D) 1 (sourceMark s) := by
    unfold tiltedSourceRow
    field_simp [(sub_pos.mpr hrl1).ne']
    ring
  rw [hid]
  exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hr1) (sub_pos.mpr hrl1).le) hlo)
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hrl) (sub_pos.mpr hrl1).le) (by simpa using hhi))

#print axioms Cell.check_sound
#print axioms leafCheck_sound
end ForestUnimodality.TiltedSource
