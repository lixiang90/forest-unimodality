import ForestUnimodality.MessagePriceSpline

/-! Exact endpoint checks for current-message prices on a whole probability
cell. Every intersected common spline segment is covered, including knots. -/
namespace ForestUnimodality.MessagePriceSpline

@[ext] theorem RealValues.ext {a b : RealValues}
    (hu : a.u=b.u) (hv : a.v=b.v) (hs : a.s=b.s) (ht : a.tau=b.tau) : a=b := by
  cases a
  cases b
  simp_all

def Segment.atRat (c : Segment) (x : ℚ) : Values :=
  let t := (x-c.lo)/(c.hi-c.lo)
  ⟨(1-t)*c.left.u+t*c.right.u,(1-t)*c.left.v+t*c.right.v,
    (1-t)*c.left.s+t*c.right.s,(1-t)*c.left.tau+t*c.right.tau⟩

def Values.toReal (v : Values) : RealValues := ⟨v.u,v.v,v.s,v.tau⟩

noncomputable def RealValues.lerp (a b : RealValues) (t : ℝ) : RealValues :=
  ⟨(1-t)*a.u+t*b.u,(1-t)*a.v+t*b.v,(1-t)*a.s+t*b.s,(1-t)*a.tau+t*b.tau⟩

theorem Segment.atRat_cast (c : Segment) (x : ℚ) :
    (c.atRat x).toReal=c.atReal x := by
  ext <;> simp [Segment.atRat,Segment.atReal,Values.toReal]

theorem Segment.atReal_affine (c : Segment) (lo hi t : ℝ) :
    c.atReal ((1-t)*lo+t*hi)=(c.atReal lo).lerp (c.atReal hi) t := by
  ext <;> dsimp only [Segment.atReal,RealValues.lerp]
  all_goals simp only [div_eq_mul_inv]; ring

structure CellBounds where
  u : ℚ
  v : ℚ
  s : ℚ
  tauLo : ℚ
  tauHi : ℚ

def CellBounds.contains (B : CellBounds) (x : Values) : Prop :=
  B.u≤x.u ∧ B.v≤x.v ∧ B.s≤x.s ∧ B.tauLo≤x.tau ∧ x.tau≤B.tauHi

def CellBounds.containsReal (B : CellBounds) (x : RealValues) : Prop :=
  (B.u:ℝ)≤x.u ∧ (B.v:ℝ)≤x.v ∧ (B.s:ℝ)≤x.s ∧ (B.tauLo:ℝ)≤x.tau ∧ x.tau≤B.tauHi

instance (B : CellBounds) (x : Values) : Decidable (B.contains x) := by
  unfold CellBounds.contains; infer_instance

theorem CellBounds.contains_cast {B : CellBounds} {x : Values} (h : B.contains x) :
    B.containsReal x.toReal := by
  unfold CellBounds.contains at h
  dsimp only [CellBounds.containsReal,Values.toReal]
  exact_mod_cast h

theorem CellBounds.contains_lerp {B : CellBounds} {a b : RealValues} {t : ℝ}
    (ha : B.containsReal a) (hb : B.containsReal b) (ht : t∈Set.Icc (0:ℝ) 1) :
    B.containsReal (a.lerp b t) := by
  have lower {l x y : ℝ} (hx : l≤x) (hy : l≤y) : l≤(1-t)*x+t*y := by
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2),mul_le_mul_of_nonneg_left hy ht.1]
  have upper {u x y : ℝ} (hx : x≤u) (hy : y≤u) : (1-t)*x+t*y≤u := by
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2),mul_le_mul_of_nonneg_left hy ht.1]
  exact ⟨lower ha.1 hb.1,lower ha.2.1 hb.2.1,lower ha.2.2.1 hb.2.2.1,
    lower ha.2.2.2.1 hb.2.2.2.1,upper ha.2.2.2.2 hb.2.2.2.2⟩

def CellBounds.segmentCheck (B : CellBounds) (lo hi : ℚ) (c : Segment) : Bool :=
  if max lo c.lo≤min hi c.hi then
    decide (B.contains (c.atRat (max lo c.lo)) ∧ B.contains (c.atRat (min hi c.hi)))
  else true

def CellBounds.check (B : CellBounds) (P : Parameters) (lo hi : ℚ) : Bool :=
  P.pieces.all (B.segmentCheck lo hi)

theorem CellBounds.segmentCheck_sound {B : CellBounds} {lo hi : ℚ} {c : Segment}
    (hc : B.segmentCheck lo hi c=true) {x : ℝ}
    (hx : x∈Set.Icc (lo:ℝ) (hi:ℝ)) (hxc : x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    B.containsReal (c.atReal x) := by
  have hl : ((max lo c.lo:ℚ):ℝ)≤x := by
    simpa only [Rat.cast_max] using max_le hx.1 hxc.1
  have hh : x≤((min hi c.hi:ℚ):ℝ) := by
    simpa only [Rat.cast_min] using le_min hx.2 hxc.2
  have hlh : max lo c.lo≤min hi c.hi := by exact_mod_cast hl.trans hh
  have hends : B.contains (c.atRat (max lo c.lo)) ∧ B.contains (c.atRat (min hi c.hi)) := by
    simpa only [CellBounds.segmentCheck,if_pos hlh,decide_eq_true_eq] using hc
  have ha := contains_cast hends.1
  have hb := contains_cast hends.2
  rw [Segment.atRat_cast] at ha hb
  rcases lt_or_eq_of_le hlh with hlt|heq
  · have hd : (0:ℝ)<((min hi c.hi:ℚ):ℝ)-(max lo c.lo:ℚ) := by exact_mod_cast sub_pos.mpr hlt
    let t : ℝ := (x-(max lo c.lo:ℚ))/((min hi c.hi:ℚ)-(max lo c.lo:ℚ))
    have ht : t∈Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hl) hd.le,(div_le_one hd).mpr (by linarith)⟩
    have he : (1-t)*(max lo c.lo:ℚ)+t*(min hi c.hi:ℚ)=x := by
      dsimp [t]
      field_simp
      ring
    have hblend := contains_lerp ha hb ht
    rw [←Segment.atReal_affine,he] at hblend
    exact hblend
  · have hxe : x=((max lo c.lo:ℚ):ℝ) := le_antisymm (hh.trans_eq (by rw [heq])) hl
    rwa [hxe]

theorem CellBounds.check_sound {B : CellBounds} {P : Parameters} {lo hi : ℚ}
    (hP : P.check=true) (hB : B.check P lo hi=true) {x : ℝ}
    (hcap : x∈Set.Icc (0:ℝ) ((P.upper:ℝ)/(1+(P.upper:ℝ))))
    (hx : x∈Set.Icc (lo:ℝ) (hi:ℝ)) : B.containsReal (evaluate P.pieces x) := by
  obtain ⟨c,hc,hxc,he⟩ := P.selected_segment hP hcap
  rw [he]
  exact segmentCheck_sound ((List.all_eq_true.mp hB) c hc) hx hxc

#print axioms CellBounds.check_sound
end ForestUnimodality.MessagePriceSpline
