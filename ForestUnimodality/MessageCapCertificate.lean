import ForestUnimodality.MessageCells

/-! The probability-cap boundary has response exactly one. Only its true
point-response polynomial is checked; no invalid all-response extension is
required at the vanishing logarithmic capacity. -/
namespace ForestUnimodality.MessageCells
open MessagePriceSpline MessagePolynomialEnvelope BernsteinCertificate

def capLower (D : Domain) : ℚ := 1/(1+D.b*(1-SelectionSource.probabilityCap D))
def capParent (D : Domain) : ℚ :=
  D.b*(1-SelectionSource.probabilityCap D)/(1+D.b*(1-SelectionSource.probabilityCap D))

def capBounds (D : Domain) (hh logLower : ℚ) : MessagePolynomialEnvelope.Bounds :=
  ⟨0,0,hh,1-SelectionSource.probabilityCap D,0,
    SelectionSource.affineSlope (SelectionSource.probabilityCap D) (SelectionSource.probabilityCap D) true,
    SelectionSource.affineIntercept (SelectionSource.probabilityCap D) true,logLower,0,0,0,0⟩

structure CapBranchCertificate where
  lower : BernsteinCertificate.Certificate
  upper : BernsteinCertificate.Certificate

def CapBranchCertificate.check (w : CapBranchCertificate) (c : Segment)
    (P : MessagePriceSpline.Parameters) (D : Domain) (hh logLower : ℚ) (moving : Bool) : Bool :=
  if c.lo≤c.parentUpper (capParent D) ∧
      c.branchLeft (capLower D) (capParent D) moving≤c.branchRight 1 moving then
    intervalCheck (positiveQuad (polynomialParameters P) (capBounds D hh logLower)
      (c.parentPolynomials (c.parentA moving) (Segment.parentB moving))).C
      (c.branchLeft (capLower D) (capParent D) moving) (c.branchRight 1 moving) w.lower &&
    intervalCheck (positiveQuad (polynomialParameters P) (capBounds D hh logLower)
      (c.parentPolynomials (c.parentUpper (capParent D)) 0)).C
      (c.branchLeft (capLower D) (capParent D) moving) (c.branchRight 1 moving) w.upper
  else true

structure CapParentCertificate where
  segment : Segment
  fixed : CapBranchCertificate
  moving : CapBranchCertificate

def CapParentCertificate.check (w : CapParentCertificate)
    (P : MessagePriceSpline.Parameters) (D : Domain) (hh logLower : ℚ) : Bool :=
  w.fixed.check w.segment P D hh logLower false &&
    w.moving.check w.segment P D hh logLower true

theorem cap_polynomial_nonneg {P : MessagePriceSpline.Parameters} {D : Domain} {hh logLower lo hi : ℚ}
    {c : Segment} {a b : ℚ} {w : BernsteinCertificate.Certificate}
    (hw : intervalCheck (positiveQuad (polynomialParameters P) (capBounds D hh logLower)
      (c.parentPolynomials a b)).C lo hi w=true) {r : ℝ}
    (hr : r∈Set.Icc (lo:ℝ) (hi:ℝ)) :
    0≤messageSourceMarkedEnvelope P.toReal (capBounds D hh logLower).toReal r 1
      (c.atReal ((a:ℝ)+(b:ℝ)*r)).u (c.atReal ((a:ℝ)+(b:ℝ)*r)).v
      (c.atReal ((a:ℝ)+(b:ℝ)*r)).s (c.atReal ((a:ℝ)+(b:ℝ)*r)).tau := by
  have hpoly := intervalCheck_sound hw hr
  have he := positiveQuad_identity (polynomialParameters P) (capBounds D hh logLower)
    (c.parentPolynomials a b) r 0 (by norm_num)
  simp only [add_zero,ParametricQuadratic.Quad.value,zero_pow (by decide : 2≠0),mul_zero,zero_add] at he
  rw [←he] at hpoly
  rwa [c.polynomial_envelope_eq_marked a b r 1 _ _ P.toReal rfl rfl rfl rfl] at hpoly

theorem CapParentCertificate.check_sound {w : CapParentCertificate} {P : MessagePriceSpline.Parameters}
    {D : Domain} {hh logLower : ℚ} (hw : w.check P D hh logLower=true) {r : ℝ}
    (hr : r∈Set.Icc (capLower D:ℝ) 1)
    (hinter : max (w.segment.lo:ℝ) (1-r)≤min (w.segment.hi:ℝ) (capParent D:ℝ)) :
    (let f := fun x=>messageSourceMarkedEnvelope P.toReal (capBounds D hh logLower).toReal r 1
      (w.segment.atReal x).u (w.segment.atReal x).v (w.segment.atReal x).s (w.segment.atReal x).tau
    0≤f (max (w.segment.lo:ℝ) (1-r)) ∧ 0≤f (min (w.segment.hi:ℝ) (capParent D:ℝ))) := by
  obtain ⟨moving,hr',he,hlo⟩ := w.segment.parent_branch_cover (capLower D) 1 (capParent D)
    (by simpa only [Rat.cast_one] using hr) hinter
  have hchecks := Bool.and_eq_true_iff.mp hw
  have hchecked (z : CapBranchCertificate)
      (hz : z.check w.segment P D hh logLower moving=true) :
      intervalCheck (positiveQuad (polynomialParameters P) (capBounds D hh logLower)
        (w.segment.parentPolynomials (w.segment.parentA moving) (Segment.parentB moving))).C
        (w.segment.branchLeft (capLower D) (capParent D) moving)
        (w.segment.branchRight 1 moving) z.lower=true ∧
      intervalCheck (positiveQuad (polynomialParameters P) (capBounds D hh logLower)
        (w.segment.parentPolynomials (w.segment.parentUpper (capParent D)) 0)).C
        (w.segment.branchLeft (capLower D) (capParent D) moving)
        (w.segment.branchRight 1 moving) z.upper=true := by
    have hord : w.segment.branchLeft (capLower D) (capParent D) moving≤
        w.segment.branchRight 1 moving := by exact_mod_cast hr'.1.trans hr'.2
    have hactive := And.intro hlo hord
    simpa only [CapBranchCertificate.check,if_pos hactive,Bool.and_eq_true_iff] using hz
  have hpos : ∃z:CapBranchCertificate,z.check w.segment P D hh logLower moving=true := by
    cases moving with
    | false => exact ⟨w.fixed,hchecks.1⟩
    | true => exact ⟨w.moving,hchecks.2⟩
  obtain ⟨z,hz⟩ := hpos
  obtain ⟨hl,hu⟩ := hchecked z hz
  have hl' := cap_polynomial_nonneg hl hr'
  have hu' := cap_polynomial_nonneg hu hr'
  rw [he] at hl'
  simp only [Rat.cast_zero,zero_mul,add_zero,Segment.parentUpper,Rat.cast_min] at hu'
  exact ⟨hl',hu'⟩

structure CapCertificate where
  hh : ℚ
  exactLog : SourceLogWitness
  logRight : SourceLogWitness
  logComplement : SourceLogWitness
  logLower : ℚ
  parents : List CapParentCertificate

def CapCertificate.Accepts (w : CapCertificate) (P : MessagePriceSpline.Parameters) (D : Domain) : Prop :=
  D.lower=P.lower ∧ D.b=P.upper ∧ 0≤w.hh ∧
  w.exactLog.check (1/(1-SelectionSource.probabilityCap D))=true ∧
  SelectionSource.probabilityCap D≤w.hh*w.exactLog.lo ∧
  w.logRight.check (SelectionSource.probabilityCap D)=true ∧
  w.logComplement.check (1-SelectionSource.probabilityCap D)=true ∧
  w.logLower*SelectionSource.probabilityCap D≤P.Dn-P.ell*
    (w.logRight.hi-2*w.logComplement.lo-D.lowerLog.lo) ∧
  w.parents.map CapParentCertificate.segment=P.pieces ∧
  w.parents.all (fun e=>e.check P D w.hh w.logLower)=true

instance (w : CapCertificate) (P : MessagePriceSpline.Parameters) (D : Domain) : Decidable (w.Accepts P D) := by
  unfold CapCertificate.Accepts
  infer_instance

def CapCertificate.check (w : CapCertificate) (P : MessagePriceSpline.Parameters) (D : Domain) : Bool :=
  decide (w.Accepts P D)

theorem CapCertificate.check_sound {w : CapCertificate} {P : MessagePriceSpline.Parameters} {D : Domain}
    (hw : w.check P D=true) (hP : P.check=true) (hD : D.Valid)
    {r parentp : ℝ} (hr : 1/(1+(D.b:ℝ)*(1-(SelectionSource.probabilityCap D:ℝ)))≤r)
    (hr1 : r≤1) (hparentLo : 1-r≤parentp) (hparentHi : parentp≤(capParent D:ℝ)) :
    0≤messageSourceScalarRow P.toReal D.lower D.b (SelectionSource.probabilityCap D) r 1 parentp := by
  have hh : w.Accepts P D := of_decide_eq_true hw
  rcases hh with ⟨hlower,hupper,hhh,hexact,hprice,hlogR,hlogC,hlog,hparents,hchecks⟩
  have hA := MessagePriceSpline.Parameters.check_sound hP
  have hP' : P.Accepts := of_decide_eq_true hP
  let q : ℝ := SelectionSource.probabilityCap D
  have hqeq : q=(D.b:ℝ)/(1+(D.b:ℝ)) := by simp [q,SelectionSource.probabilityCap]
  have hb := hD.b_pos
  have hb1 : 0<1+(D.b:ℝ) := by linarith
  have hq : 0<q := by rw [hqeq]; positivity
  have hq1 : q<1 := by rw [hqeq]; exact (div_lt_one hb1).mpr (by linarith)
  have hden : 0<1+(D.b:ℝ)*(1-q) := by positivity
  have hr0 : 0≤r := (div_nonneg (by norm_num) hden.le).trans hr
  have hrlo : (capLower D:ℝ)≤r := by
    simpa only [capLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub] using hr
  have hparentcap : parentp≤(P.upper:ℝ)/(1+(P.upper:ℝ)) := by
    rw [←hupper]
    apply sourceParentProbability_le_cap hb hq.le hq1
    simpa only [capParent,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_add] using hparentHi
  have he := (w.exactLog.certificate.check_sound hexact).1
  push_cast at he
  have hH : sourceExactH q≤(w.hh:ℝ) := sourceExactH_upper_of_log_lower hq hq1
    (by exact_mod_cast hhh) he (by dsimp only [q]; exact_mod_cast hprice)
  have hlogRr := (w.logRight.certificate.check_sound hlogR).2
  have hlogCr := (w.logComplement.certificate.check_sound hlogC).1
  push_cast at hlogRr hlogCr
  have hlogbound : (w.logLower:ℝ)≤sourceLogPenalty D.lower P.toReal.Dn P.toReal.ell q := by
    have hg := sourceLogReference_upper hlogRr hlogCr hD.lowerLog_lo
    have hl : (w.logLower:ℝ)*q≤(P.Dn:ℝ)-(P.ell:ℝ)*
        ((w.logRight.hi:ℝ)-2*(w.logComplement.lo:ℝ)-(D.lowerLog.lo:ℝ)) := by
      dsimp only [q]
      exact_mod_cast hlog
    unfold sourceLogPenalty
    apply (le_div_iff₀ hq).mpr
    exact hl.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hg hA.2.2.2.2.2.1) _)
  have hT : sourceLogCapacity D.b q=0 := by
    unfold sourceLogCapacity
    have hratio : (D.b:ℝ)*(1-q)/q=1 := by
      rw [hqeq]
      field_simp [hb.ne',hb1.ne']
      ring
    rw [hratio,Real.log_one]
  have hcapacities : (0:ℝ)≤1/(q*sourceLogCapacity D.b q) ∧
      (0:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b q) := by
    simp [hT,sourceOddsCapacity]
  have hphi : 0≤sourcePhi D.lower D.b q := by
    unfold sourcePhi
    exact mul_nonneg (div_nonneg (div_nonneg hb.le hb1.le)
      (Real.log_pos (by linarith : (1:ℝ)<1+(D.b:ℝ))).le) (le_max_left _ _)
  have hcurrent := hA.2.2.2.2.2.2 q ⟨hq.le,by rw [←hupper]; exact hqeq.le⟩
  apply P.scalar_nonneg_of_clipped_segments hP D.lower D.b q r 1 (1-r) (capParent D) parentp
    ⟨(sub_nonneg.mpr hr1).trans hparentLo,hparentcap⟩ hparentLo hparentHi
  intro seg hseg hinter
  have hmem : seg∈w.parents.map CapParentCertificate.segment := by rw [hparents]; exact hseg
  obtain ⟨e,hem,hes⟩ := List.mem_map.mp hmem
  have hen := CapParentCertificate.check_sound ((List.all_eq_true.mp hchecks) e hem) ⟨hrlo,hr1⟩
  rw [hes] at hen
  have hends := hen hinter
  have hsegcheck := (List.all_eq_true.mp hP'.2.2.2.2.2.2.1) seg hseg
  have hrow {x : ℝ} (hx : x∈Set.Icc (seg.lo:ℝ) (seg.hi:ℝ))
      (hen : 0≤messageSourceMarkedEnvelope P.toReal (capBounds D w.hh w.logLower).toReal r 1
        (seg.atReal x).u (seg.atReal x).v (seg.atReal x).s (seg.atReal x).tau) :
      0≤messageSourceSegmentRow P.toReal D.lower D.b q r 1 seg x := by
    have hnon := Segment.check_sound hsegcheck hx
    apply hen.trans
    apply messageSourceMarkedEnvelope_le P.toReal _ _ _ _ _ _ _ _ _ _
      hA.2.2.1 hA.2.2.2.2.1 hr0 hr1 (by norm_num [capBounds,Bounds.toReal])
      (by norm_num [capBounds,Bounds.toReal]) (by norm_num [capBounds,Bounds.toReal])
      (by norm_num [capBounds,Bounds.toReal]) (by norm_num [capBounds,Bounds.toReal])
      (by simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hcurrent.1)
      (by simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hcurrent.2.1)
      (by simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hcurrent.2.2)
      hnon.1 hnon.2.1 hnon.2.2
      (by simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hcapacities.1)
      (by simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hcapacities.2) hH
    · simp only [capBounds,Bounds.toReal,Rat.cast_sub,Rat.cast_one]; exact le_rfl
    · simpa only [capBounds,Bounds.toReal,Rat.cast_zero] using hphi
    · exact SelectionSource.affine_lower D hb (SelectionSource.probabilityCap D) true (le_refl _) hr0
    · exact hlogbound
    · simp
  exact ⟨hrow ⟨le_max_left _ _,hinter.trans (min_le_left _ _)⟩ hends.1,
    hrow ⟨(le_max_left _ _).trans hinter,min_le_left _ _⟩ hends.2⟩

#print axioms CapParentCertificate.check_sound
#print axioms CapCertificate.check_sound
end ForestUnimodality.MessageCells
