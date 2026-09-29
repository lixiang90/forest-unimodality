import ForestUnimodality.MessageParentPolynomials

/-! Exact retention branches for the moving parent lower endpoint. No
retention value or degenerate endpoint is dropped by the finite split. -/
namespace ForestUnimodality.MessagePriceSpline

def Segment.parentUpper (c : Segment) (upper : ℚ) : ℚ := min c.hi upper

def Segment.branchLeft (c : Segment) (rl upper : ℚ) (moving : Bool) : ℚ :=
  if moving then max rl (1-c.parentUpper upper)
  else max (max rl (1-c.parentUpper upper)) (1-c.lo)

def Segment.branchRight (c : Segment) (rh : ℚ) (moving : Bool) : ℚ :=
  if moving then min rh (1-c.lo) else rh

def Segment.parentA (c : Segment) (moving : Bool) : ℚ := if moving then 1 else c.lo
def Segment.parentB (moving : Bool) : ℚ := if moving then -1 else 0

theorem Segment.parent_branch_cover (c : Segment) (rl rh upper : ℚ) {r : ℝ}
    (hr : r∈Set.Icc (rl:ℝ) (rh:ℝ))
    (hinter : max (c.lo:ℝ) (1-r)≤min (c.hi:ℝ) (upper:ℝ)) :
    ∃moving:Bool,
      r∈Set.Icc (c.branchLeft rl upper moving:ℝ) (c.branchRight rh moving:ℝ) ∧
      (c.parentA moving:ℝ)+(Segment.parentB moving:ℝ)*r=max (c.lo:ℝ) (1-r) ∧
      c.lo≤c.parentUpper upper := by
  have hclo : (c.lo:ℝ)≤min (c.hi:ℝ) (upper:ℝ) := (le_max_left _ _).trans hinter
  have hlower : 1-r≤min (c.hi:ℝ) (upper:ℝ) := (le_max_right _ _).trans hinter
  have hbase : ((max rl (1-c.parentUpper upper):ℚ):ℝ)≤r := by
    simp only [Rat.cast_max,Rat.cast_sub,Rat.cast_one,Segment.parentUpper,Rat.cast_min]
    exact max_le hr.1 (by linarith)
  have hclo' : c.lo≤c.parentUpper upper := by
    unfold Segment.parentUpper
    exact_mod_cast hclo
  by_cases hm : r≤1-(c.lo:ℝ)
  · refine ⟨true,?_,?_,hclo'⟩
    · simpa only [Segment.branchLeft,Segment.branchRight,if_true,Rat.cast_min,Rat.cast_sub,
        Rat.cast_one,Set.mem_Icc] using And.intro hbase (le_min hr.2 hm)
    · simp only [Segment.parentA,Segment.parentB,if_true,Rat.cast_one,Rat.cast_neg,
        neg_mul,one_mul]
      rw [max_eq_right (by linarith)]
      ring
  · refine ⟨false,?_,?_,hclo'⟩
    · simp only [Segment.branchLeft,Segment.branchRight,Bool.false_eq_true,if_false,
        Rat.cast_max,Rat.cast_sub,Rat.cast_one]
      exact ⟨max_le (by simpa only [Rat.cast_max,Rat.cast_sub,Rat.cast_one] using hbase)
        (by linarith),hr.2⟩
    · simp only [Segment.parentA,Segment.parentB,Bool.false_eq_true,if_false,Rat.cast_zero,
        zero_mul,add_zero]
      rw [max_eq_left (by linarith)]

end ForestUnimodality.MessagePriceSpline

namespace ForestUnimodality.MessagePolynomialEnvelope
open ParametricQuadratic

structure Certificate where
  negative : RayCertificate
  middle : UnitCertificate
  positive : RayCertificate

def Certificate.check (c : Certificate) (P : Parameters)
    (Bbelow Babove : Bounds) (Q : ParentPrices) (lo hi : ℚ) : Bool :=
  c.negative.check (negativeQuad P Bbelow Q) lo hi &&
    c.middle.check (middleQuad P Bbelow Q) lo hi &&
    c.positive.check (positiveQuad P Babove Q) lo hi

noncomputable def signedEnvelope (P : Parameters) (Bbelow Babove : Bounds)
    (Q : ParentPrices) (r z : ℝ) : ℝ :=
  if z≤1 then envelope P Bbelow Q r z else envelope P Babove Q r z

theorem Certificate.check_sound {c : Certificate} {P : Parameters}
    {Bbelow Babove : Bounds} {Q : ParentPrices} {lo hi : ℚ}
    (hc : c.check P Bbelow Babove Q lo hi=true)
    {r z : ℝ} (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ)) :
    0≤signedEnvelope P Bbelow Babove Q r z := by
  have hh : c.negative.check (negativeQuad P Bbelow Q) lo hi=true ∧
      c.middle.check (middleQuad P Bbelow Q) lo hi=true ∧
      c.positive.check (positiveQuad P Babove Q) lo hi=true := by
    simpa only [Certificate.check,Bool.and_eq_true_iff,and_assoc] using hc
  by_cases hz : z≤1
  · rw [signedEnvelope,if_pos hz]
    by_cases hz0 : z≤0
    · exact negative_check_sound hh.1 hr hz0
    · exact middle_check_sound hh.2.1 hr ⟨(lt_of_not_ge hz0).le,hz⟩
  · rw [signedEnvelope,if_neg hz]
    exact positive_check_sound hh.2.2 hr (lt_of_not_ge hz).le

#print axioms MessagePriceSpline.Segment.parent_branch_cover
#print axioms Certificate.check_sound
end ForestUnimodality.MessagePolynomialEnvelope
