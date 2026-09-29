import ForestUnimodality.ForestSourceCertificate

/-! Computable rational parameters with an explicit bridge to the real
forest-source row. No source estimate is included in the definition. -/
namespace ForestUnimodality

structure RationalSourceParameters where
  A : ℚ
  C : ℚ
  u0 : ℚ
  u1 : ℚ
  v0 : ℚ
  v1 : ℚ
  w : ℚ
  t : ℚ
  s : ℚ
  ell : ℚ

noncomputable def RationalSourceParameters.toReal (P : RationalSourceParameters) : SourceRowParameters where
  A := P.A
  C := P.C
  logPrice := P.ell
  phiPrice := P.w
  responsePrice := P.t
  blockingPrice := P.s
  positivePrice := fun a => if a=1 then P.u1 else P.u0
  negativePrice := fun a => if a=1 then P.v1 else P.v0

def RationalSourceParameters.Admissible (P : RationalSourceParameters) : Prop :=
  0≤P.ell ∧ 0≤P.w ∧ 0≤P.s ∧ 0≤P.u0 ∧ 0≤P.u1 ∧ 0≤P.v0 ∧ 0≤P.v1

instance (P : RationalSourceParameters) : Decidable P.Admissible := by
  unfold RationalSourceParameters.Admissible
  infer_instance

def RationalSourceParameters.admissibleCheck (P : RationalSourceParameters) : Bool := decide P.Admissible

theorem RationalSourceParameters.admissible_sound {P : RationalSourceParameters}
    (h : P.admissibleCheck=true) : P.toReal.Admissible := by
  have hp : P.Admissible := of_decide_eq_true h
  rcases hp with ⟨he,hw,hs,hu0,hu1,hv0,hv1⟩
  unfold SourceRowParameters.Admissible
  dsimp only [toReal]
  refine ⟨by exact_mod_cast he, by exact_mod_cast hw, by exact_mod_cast hs, ?_, ?_⟩
  · intro a
    split
    · exact_mod_cast hu1
    · exact_mod_cast hu0
  · intro a
    split
    · exact_mod_cast hv1
    · exact_mod_cast hv0

#print axioms RationalSourceParameters.admissible_sound
end ForestUnimodality

