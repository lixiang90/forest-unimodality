import ForestUnimodality.SelectionSourceBounds
import ForestUnimodality.MessageSourceEnvelope

/-! Constant-price selection sources with the exact logarithmic capacity.
The existing retention/response polynomial certificates are reusable;
only their comparison to the true scalar uses the stronger capacity. -/
namespace ForestUnimodality.ExactSelectionSource
open SelectionSource
variable {V : Type*} [DecidableEq V]

noncomputable def toMessage (P : Parameters) : MessageSourceParameters where
  CJ := P.CJ
  Cmu := P.Cmu
  w := P.w
  t := P.t
  u := fun _ => P.u
  v := fun _ => P.v
  s := fun _ => P.s
  tau := fun _ => 0
  Dn := 0
  ell := 0

noncomputable def messageBounds (P : Parameters) (d : Bounds) : MessageEnvelopeBounds where
  L := d.L
  H := d.H
  hh := d.hh
  dd := d.dd
  phi := d.phi
  selectionSlope := d.fs
  selectionIntercept := d.fb
  logLower := 0
  u := P.u
  v := P.v
  s := P.s
  tau := 0

theorem toMessage_admissible (P : Parameters) (hP : P.check = true) (b : ℝ) :
    (toMessage P).Admissible b := by
  dsimp only [MessageSourceParameters.Admissible, toMessage]
  have hs : P.Accepts := of_decide_eq_true hP
  rcases hs with ⟨_, _, hu, hv, hw, hs⟩
  refine ⟨?_, le_rfl, fun _ _ => ⟨?_, ?_, ?_⟩⟩
  · exact_mod_cast hw
  · exact_mod_cast hu
  · exact_mod_cast hv
  · exact_mod_cast hs

theorem envelope_eq_message (P : Parameters) (d : Bounds) (r z parentp : ℝ) :
    envelope P d r z = messageSourceEnvelope (toMessage P) (messageBounds P d) r z parentp := by
  unfold envelope messageSourceEnvelope toMessage messageBounds
  ring

theorem envelope_le (P : Parameters) (d : Bounds) (hP : P.check = true)
    {lower b p r z parentp : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL0 : (0 : ℝ) ≤ d.L) (hH0 : (0 : ℝ) ≤ d.H)
    (hcap : (d.L : ℝ) ≤ 1 / (p * sourceLogCapacity b p) ∧
      (d.H : ℝ) ≤ 1 / sourceOddsCapacity b (sourceLogCapacity b p))
    (hphi : (d.phi : ℝ) ≤ sourcePhi lower b p)
    (hhh : sourceExactH p ≤ (d.hh : ℝ)) (hdd : 1 - p ≤ (d.dd : ℝ))
    (hf : (d.fs : ℝ) * r + d.fb ≤ MarginalSelectionBound.selectionFraction (b / (1+b)) (p*r)) :
    envelope P d r z ≤ messageSourceScalarRow (toMessage P) lower b p r z parentp := by
  have hs : P.Accepts := of_decide_eq_true hP
  rcases hs with ⟨hCJ, _, hu, hv, hw, hs⟩
  have huR : (0 : ℝ) ≤ P.u := by exact_mod_cast hu
  have hvR : (0 : ℝ) ≤ P.v := by exact_mod_cast hv
  have hsR : (0 : ℝ) ≤ P.s := by exact_mod_cast hs
  rw [envelope_eq_message]
  apply messageSourceEnvelope_le (toMessage P) (messageBounds P d) lower b p r z parentp
    (by dsimp only [toMessage]; exact_mod_cast hCJ)
    (by dsimp only [toMessage]; exact_mod_cast hw) hr0 hr1 hL0 hH0
    huR hvR hsR le_rfl le_rfl le_rfl huR hvR hsR
    hcap.1 hcap.2 hhh hdd hphi hf
  · simp [messageBounds, sourceLogPenalty, toMessage]
  · simp [messageBounds, toMessage]

theorem forest_variance (P : Parameters) (hP : P.check = true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {lower b activity : ℝ} (hlower : 0 < lower)
    (hlo : lower ≤ activity) (hhi : activity ≤ b)
    (hvalid : MessageSourceRowValid (toMessage P) lower b) :
    hardCoreVariance G S activity ≤
      (P.CJ : ℝ) * hardCoreMarginalSelectionScore G S activity b +
      (P.Cmu : ℝ) * hardCoreMean G S activity := by
  have h := forest_message_variance_of_scalar_certificate G hG S
    hlower (hlower.trans_le hlo) hhi (toMessage P) (toMessage_admissible P hP b)
    (Or.inr hlo) hvalid
  simpa [toMessage] using h

theorem variance_le_mass (P : Parameters) (hP : P.check = true)
    {G : SimpleGraph V} {S B : Finset V} {lower b activity : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B activity) (hG : G.IsAcyclic)
    (hlower : 0 < lower) (hlo : lower ≤ activity) (hhi : activity ≤ b)
    (hvalid : MessageSourceRowValid (toMessage P) lower b) :
    hardCoreVariance G S activity ≤
      ((P.CJ : ℝ) + 2 * (P.Cmu : ℝ)) * hardCoreOccupiedMass G S B activity := by
  have hp := Parameters.check_sound hP
  have h := hB.variance_le_mass_of_message_source hG
    hlower (hlower.trans_le hlo) hhi (toMessage P) (toMessage_admissible P hP b)
    hp.2.1 hp.2.2 (Or.inr hlo) hvalid
  simpa [toMessage] using h

#print axioms envelope_le
#print axioms forest_variance
#print axioms variance_le_mass
end ForestUnimodality.ExactSelectionSource
