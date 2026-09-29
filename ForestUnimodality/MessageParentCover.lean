import ForestUnimodality.MessagePriceCellBounds

/-! Complete same-parent coverage by clipped common price segments. Checking
both ends of each nonempty intersection suffices for every feasible parent. -/
namespace ForestUnimodality
open MessagePriceSpline

theorem sourceParentProbability_le_cap {b p parentp : ℝ}
    (hb : 0<b) (hp : 0≤p) (hp1 : p<1)
    (hparent : parentp≤b*(1-p)/(1+b*(1-p))) : parentp≤b/(1+b) := by
  have hden : 0<1+b*(1-p) := by positivity
  have hb1 : 0<1+b := by linarith
  apply hparent.trans
  apply (div_le_div_iff₀ hden hb1).mpr
  nlinarith [mul_nonneg hb.le hp]

noncomputable def messageSourceSegmentRow (P : MessageSourceParameters)
    (lower b p r d : ℝ) (c : Segment) (parentp : ℝ) : ℝ :=
  messageSourceMarkedRow P lower b p r d
    (c.atReal parentp).u (c.atReal parentp).v (c.atReal parentp).s (c.atReal parentp).tau

theorem messageSourceSegmentRow_endpoints (P : MessageSourceParameters)
    (lower b p r d lo hi parentp : ℝ) (c : Segment)
    (hlo : lo≤parentp) (hhi : parentp≤hi)
    (hleft : 0≤messageSourceSegmentRow P lower b p r d c lo)
    (hright : 0≤messageSourceSegmentRow P lower b p r d c hi) :
    0≤messageSourceSegmentRow P lower b p r d c parentp := by
  rcases lt_or_eq_of_le (hlo.trans hhi) with hlt|heq
  · let theta : ℝ := (parentp-lo)/(hi-lo)
    have ht : theta∈Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hlt).le,
        (div_le_one (sub_pos.mpr hlt)).mpr (by linarith)⟩
    have hx : (1-theta)*lo+theta*hi=parentp := by
      dsimp [theta]
      field_simp
      ring
    have hv := c.atReal_affine lo hi theta
    rw [hx] at hv
    unfold messageSourceSegmentRow at hleft hright ⊢
    rw [hv]
    exact messageSourceMarkedRow_parent_nonneg P lower b p r d theta _ _ _ _ _ _ _ _ ht hleft hright
  · have hx : parentp=lo := le_antisymm (hhi.trans_eq heq.symm) hlo
    rwa [hx]

/-- A finite union of common price segments covers the whole parent domain.
The endpoint hypothesis is required only for nonempty intersections. -/
theorem MessagePriceSpline.Parameters.scalar_nonneg_of_clipped_segments
    (P : Parameters) (hP : P.check=true) (lower b p r d parentLo parentHi parentp : ℝ)
    (hparentCap : parentp∈Set.Icc (0:ℝ) ((P.upper:ℝ)/(1+(P.upper:ℝ))))
    (hparentLo : parentLo≤parentp) (hparentHi : parentp≤parentHi)
    (hends : ∀c∈P.pieces, max (c.lo:ℝ) parentLo≤min (c.hi:ℝ) parentHi →
      0≤messageSourceSegmentRow P.toReal lower b p r d c (max (c.lo:ℝ) parentLo) ∧
      0≤messageSourceSegmentRow P.toReal lower b p r d c (min (c.hi:ℝ) parentHi)) :
    0≤messageSourceScalarRow P.toReal lower b p r d parentp := by
  obtain ⟨c,hc,hpc,he⟩ := P.selected_segment hP hparentCap
  have hl : max (c.lo:ℝ) parentLo≤parentp := max_le hpc.1 hparentLo
  have hh : parentp≤min (c.hi:ℝ) parentHi := le_min hpc.2 hparentHi
  obtain ⟨hleft,hright⟩ := hends c hc (hl.trans hh)
  have hrow := messageSourceSegmentRow_endpoints P.toReal lower b p r d _ _ parentp c hl hh hleft hright
  change 0≤messageSourceMarkedRow P.toReal lower b p r d
    (evaluate P.pieces parentp).u (evaluate P.pieces parentp).v
    (evaluate P.pieces parentp).s (evaluate P.pieces parentp).tau
  rw [he]
  exact hrow

#print axioms sourceParentProbability_le_cap
#print axioms MessagePriceSpline.Parameters.scalar_nonneg_of_clipped_segments
end ForestUnimodality
