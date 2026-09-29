import ForestUnimodality.MessageVarianceSource

/-! All four prices are interpolated at the same parent probability. This
preserves the coupling used by the message-dependent scalar certificate. -/
namespace ForestUnimodality

theorem messageSourceMarkedRow_parent_lerp
    (P : MessageSourceParameters) (lower b p r d theta : ℝ)
    (u0 v0 s0 t0 u1 v1 s1 t1 : ℝ) :
    messageSourceMarkedRow P lower b p r d
      ((1-theta)*u0+theta*u1) ((1-theta)*v0+theta*v1)
      ((1-theta)*s0+theta*s1) ((1-theta)*t0+theta*t1) =
    (1-theta)*messageSourceMarkedRow P lower b p r d u0 v0 s0 t0+
      theta*messageSourceMarkedRow P lower b p r d u1 v1 s1 t1 := by
  unfold messageSourceMarkedRow
  ring

theorem messageSourceMarkedRow_parent_nonneg
    (P : MessageSourceParameters) (lower b p r d theta : ℝ)
    (u0 v0 s0 t0 u1 v1 s1 t1 : ℝ) (ht : theta∈Set.Icc (0:ℝ) 1)
    (h0 : 0≤messageSourceMarkedRow P lower b p r d u0 v0 s0 t0)
    (h1 : 0≤messageSourceMarkedRow P lower b p r d u1 v1 s1 t1) :
    0≤messageSourceMarkedRow P lower b p r d
      ((1-theta)*u0+theta*u1) ((1-theta)*v0+theta*v1)
      ((1-theta)*s0+theta*s1) ((1-theta)*t0+theta*t1) := by
  rw [messageSourceMarkedRow_parent_lerp]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) h0) (mul_nonneg ht.1 h1)

/-- A common affine piece for the four prices, with arbitrary signed tau. -/
def MessageSourceParameters.AffineOnParentInterval
    (P : MessageSourceParameters) (lo hi : ℝ) : Prop :=
  ∀x∈Set.Icc lo hi,
    P.u x=(1-(x-lo)/(hi-lo))*P.u lo+(x-lo)/(hi-lo)*P.u hi ∧
    P.v x=(1-(x-lo)/(hi-lo))*P.v lo+(x-lo)/(hi-lo)*P.v hi ∧
    P.s x=(1-(x-lo)/(hi-lo))*P.s lo+(x-lo)/(hi-lo)*P.s hi ∧
    P.tau x=(1-(x-lo)/(hi-lo))*P.tau lo+(x-lo)/(hi-lo)*P.tau hi

theorem messageSourceScalarRow_parent_endpoints
    (P : MessageSourceParameters) (lower b p r d lo hi x : ℝ)
    (hinterval : lo<hi) (hx : x∈Set.Icc lo hi)
    (hpiece : P.AffineOnParentInterval lo hi)
    (hlo : 0≤messageSourceScalarRow P lower b p r d lo)
    (hhi : 0≤messageSourceScalarRow P lower b p r d hi) :
    0≤messageSourceScalarRow P lower b p r d x := by
  have ht : (x-lo)/(hi-lo)∈Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hinterval).le,
      (div_le_one (sub_pos.mpr hinterval)).mpr (by linarith [hx.2])⟩
  obtain ⟨hu,hv,hs,htau⟩ := hpiece x hx
  unfold messageSourceScalarRow at hlo hhi ⊢
  rw [hu,hv,hs,htau]
  exact messageSourceMarkedRow_parent_nonneg P lower b p r d _ _ _ _ _ _ _ _ _ ht hlo hhi

/-- The same-parent feasible interval is intersected with one common affine
piece. It suffices to check its two ends, including the moving end 1-r. -/
theorem messageSourceScalarRow_parent_clipped_endpoints
    (P : MessageSourceParameters) (lower b p r d parentp left right : ℝ)
    (hleft : left≤parentp) (hright : parentp≤right)
    (hparentLo : 1-r≤parentp)
    (hparentHi : parentp≤b*(1-p)/(1+b*(1-p)))
    (hpiece : P.AffineOnParentInterval
      (max left (1-r)) (min right (b*(1-p)/(1+b*(1-p)))))
    (hlo : 0≤messageSourceScalarRow P lower b p r d (max left (1-r)))
    (hhi : 0≤messageSourceScalarRow P lower b p r d
      (min right (b*(1-p)/(1+b*(1-p))))) :
    0≤messageSourceScalarRow P lower b p r d parentp := by
  have hl : max left (1-r)≤parentp := max_le hleft hparentLo
  have hh : parentp≤min right (b*(1-p)/(1+b*(1-p))) := le_min hright hparentHi
  rcases lt_or_eq_of_le (hl.trans hh) with hlt|heq
  · exact messageSourceScalarRow_parent_endpoints P lower b p r d _ _ _ hlt ⟨hl,hh⟩ hpiece hlo hhi
  · have hx : parentp=max left (1-r) := le_antisymm (hh.trans_eq heq.symm) hl
    rwa [hx]

#print axioms messageSourceScalarRow_parent_endpoints
#print axioms messageSourceScalarRow_parent_clipped_endpoints
end ForestUnimodality
