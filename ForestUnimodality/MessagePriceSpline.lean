import ForestUnimodality.MessageParentInterpolation
import ForestUnimodality.SelectionSourceCells

/-! Exact shared piecewise-affine message prices. All four fields are
selected from one common segment at a parent probability. The finite
coverage check includes probability zero and the full probability cap. -/
namespace ForestUnimodality.MessagePriceSpline
open SourceIntervalCoverage

structure Values where
  u : ℚ
  v : ℚ
  s : ℚ
  tau : ℚ
  deriving DecidableEq

structure RealValues where
  u : ℝ
  v : ℝ
  s : ℝ
  tau : ℝ

structure Segment where
  lo : ℚ
  hi : ℚ
  left : Values
  right : Values
  deriving DecidableEq

noncomputable def Segment.atReal (c : Segment) (x : ℝ) : RealValues :=
  let t := (x-c.lo)/(c.hi-c.lo)
  ⟨(1-t)*c.left.u+t*c.right.u,(1-t)*c.left.v+t*c.right.v,
    (1-t)*c.left.s+t*c.right.s,(1-t)*c.left.tau+t*c.right.tau⟩

def Segment.Accepts (c : Segment) : Prop :=
  c.lo<c.hi ∧ 0≤c.left.u ∧ 0≤c.left.v ∧ 0≤c.left.s ∧
    0≤c.right.u ∧ 0≤c.right.v ∧ 0≤c.right.s

instance (c : Segment) : Decidable c.Accepts := by unfold Segment.Accepts; infer_instance

def Segment.check (c : Segment) : Bool := decide c.Accepts

theorem Segment.theta_mem {c : Segment} (h : c.lo<c.hi) {x : ℝ}
    (hx : x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    (x-c.lo)/(c.hi-c.lo)∈Set.Icc (0:ℝ) 1 := by
  have hd : (0:ℝ)<(c.hi:ℝ)-c.lo := by exact_mod_cast sub_pos.mpr h
  exact ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,
    (div_le_one hd).mpr (by linarith [hx.2])⟩

theorem Segment.check_sound {c : Segment} (hc : c.check=true) {x : ℝ}
    (hx : x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    0≤(c.atReal x).u ∧ 0≤(c.atReal x).v ∧ 0≤(c.atReal x).s := by
  have h : c.Accepts := of_decide_eq_true hc
  have ht := Segment.theta_mem h.1 hx
  have hleft : (0:ℝ)≤c.left.u ∧ (0:ℝ)≤c.left.v ∧ (0:ℝ)≤c.left.s := by
    exact_mod_cast (show (0:ℚ)≤c.left.u ∧ (0:ℚ)≤c.left.v ∧ (0:ℚ)≤c.left.s from
      ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩)
  have hright : (0:ℝ)≤c.right.u ∧ (0:ℝ)≤c.right.v ∧ (0:ℝ)≤c.right.s := by
    exact_mod_cast h.2.2.2.2
  exact ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hleft.1) (mul_nonneg ht.1 hright.1),
    add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hleft.2.1) (mul_nonneg ht.1 hright.2.1),
    add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hleft.2.2) (mul_nonneg ht.1 hright.2.2)⟩

noncomputable def evaluate : List Segment → ℝ → RealValues
  | [], _ => ⟨0,0,0,0⟩
  | c::cs, x => if (c.lo:ℝ)≤x ∧ x≤c.hi then c.atReal x else evaluate cs x

/-- Segment selection is proved from the complete cover, not from a numeric
sample or an independently chosen segment for each price field. -/
theorem evaluate_mem {cs : List Segment} {x : ℝ}
    (hcover : ∃c∈cs,x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ)) :
    ∃c∈cs,x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ) ∧ evaluate cs x=c.atReal x := by
  induction cs with
  | nil => simp at hcover
  | cons c cs ih =>
      by_cases hc : (c.lo:ℝ)≤x ∧ x≤c.hi
      · exact ⟨c,by simp,hc,by simp only [evaluate,if_pos hc]⟩
      · obtain ⟨d,hd,hx⟩ := hcover
        rcases List.mem_cons.mp hd with he|hd
        · subst d; exact (hc hx).elim
        · obtain ⟨e,he,hxe,heval⟩ := ih ⟨d,hd,hx⟩
          exact ⟨e,List.mem_cons_of_mem c he,hxe,by simpa only [evaluate,if_neg hc] using heval⟩

structure Parameters where
  lower : ℚ
  upper : ℚ
  CJ : ℚ
  Cmu : ℚ
  w : ℚ
  t : ℚ
  Dn : ℚ
  ell : ℚ
  pieces : List Segment

noncomputable def Parameters.toReal (P : Parameters) : MessageSourceParameters :=
  ⟨P.CJ,P.Cmu,P.w,P.t,(fun x=>(evaluate P.pieces x).u),
    (fun x=>(evaluate P.pieces x).v),(fun x=>(evaluate P.pieces x).s),
    (fun x=>(evaluate P.pieces x).tau),P.Dn,P.ell⟩

def Parameters.Accepts (P : Parameters) : Prop :=
  0<P.lower ∧ 0<P.upper ∧ 0≤P.CJ ∧ 0≤P.Cmu ∧ 0≤P.w ∧ 0≤P.ell ∧
    P.pieces.all Segment.check=true ∧
    SourceIntervalCoverage.check Segment.lo Segment.hi 0 (P.upper/(1+P.upper)) P.pieces=true

instance (P : Parameters) : Decidable P.Accepts := by unfold Parameters.Accepts; infer_instance

def Parameters.check (P : Parameters) : Bool := decide P.Accepts

theorem Parameters.selected_segment {P : Parameters} (hP : P.check=true) {x : ℝ}
    (hx : x∈Set.Icc (0:ℝ) ((P.upper:ℝ)/(1+(P.upper:ℝ)))) :
    ∃c∈P.pieces,x∈Set.Icc (c.lo:ℝ) (c.hi:ℝ) ∧ evaluate P.pieces x=c.atReal x := by
  have h : P.Accepts := of_decide_eq_true hP
  apply evaluate_mem
  obtain ⟨c,hc,hl,hh⟩ := check_sound_closed Segment.lo Segment.hi h.2.2.2.2.2.2.2
    (show (0:ℚ)<P.upper/(1+P.upper) by positivity [h.2.1])
    (show ((0:ℚ):ℝ)≤x by simpa using hx.1)
    (show x≤((P.upper/(1+P.upper):ℚ):ℝ) by simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_one] using hx.2)
  exact ⟨c,hc,hl,hh⟩

theorem Parameters.check_sound {P : Parameters} (hP : P.check=true) :
    0<(P.lower:ℝ) ∧ 0<(P.upper:ℝ) ∧ 0≤P.toReal.CJ ∧ 0≤P.toReal.Cmu ∧
      P.toReal.Admissible P.upper := by
  have h : P.Accepts := of_decide_eq_true hP
  refine ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,
    ?_,?_,?_,?_,?_⟩
  · change (0:ℝ)≤(P.CJ:ℝ); exact_mod_cast h.2.2.1
  · change (0:ℝ)≤(P.Cmu:ℝ); exact_mod_cast h.2.2.2.1
  · change (0:ℝ)≤(P.w:ℝ); exact_mod_cast h.2.2.2.2.1
  · change (0:ℝ)≤(P.ell:ℝ); exact_mod_cast h.2.2.2.2.2.1
  ·
    intro x hx
    obtain ⟨c,hc,hxc,he⟩ := P.selected_segment hP hx
    have hcs := (List.all_eq_true.mp h.2.2.2.2.2.2.1) c hc
    change 0≤(evaluate P.pieces x).u ∧ 0≤(evaluate P.pieces x).v ∧ 0≤(evaluate P.pieces x).s
    rw [he]
    exact c.check_sound hcs hxc

#print axioms evaluate_mem
#print axioms Parameters.check_sound
end ForestUnimodality.MessagePriceSpline
