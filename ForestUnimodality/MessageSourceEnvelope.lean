import ForestUnimodality.MessageLogPenalty
import ForestUnimodality.MessageParentInterpolation

/-! A whole-cell algebraic lower envelope for the actual stage80 scalar.
Only one parent probability is used by all four parent prices. -/
namespace ForestUnimodality
open MarginalSelectionBound

structure MessageEnvelopeBounds where
  L : ℝ
  H : ℝ
  hh : ℝ
  dd : ℝ
  phi : ℝ
  selectionSlope : ℝ
  selectionIntercept : ℝ
  logLower : ℝ
  u : ℝ
  v : ℝ
  s : ℝ
  tau : ℝ

noncomputable def messageSourceEnvelope (P : MessageSourceParameters)
    (B : MessageEnvelopeBounds) (r d parentp : ℝ) : ℝ :=
  P.CJ*r*(B.selectionSlope*r+B.selectionIntercept)+P.Cmu*r-r*B.dd*d^2+
  B.u*B.L*(max 0 (1-d))^2-P.u parentp*B.hh*(max 0 d)^2+
  B.v*B.L*(max 0 (d-1))^2-P.v parentp*B.hh*(max 0 (-d))^2+
  B.s*r*(1-d)^2*B.H-(1-r)*P.s parentp*B.dd*d^2+
  P.w*(d-1+r*B.phi)+P.t*(d-r)+
  r*B.tau*(d-1)+(1-r)*P.tau parentp*d+B.logLower

theorem messageSourceEnvelope_le (P : MessageSourceParameters) (B : MessageEnvelopeBounds)
    (lower b p r d parentp : ℝ)
    (hCJ : 0≤P.CJ) (hw : 0≤P.w) (hr0 : 0≤r) (hr1 : r≤1)
    (hL0 : 0≤B.L) (hH0 : 0≤B.H)
    (hu0 : 0≤B.u) (hv0 : 0≤B.v) (hs0 : 0≤B.s)
    (hu : B.u≤P.u p) (hv : B.v≤P.v p) (hs : B.s≤P.s p)
    (hpu : 0≤P.u parentp) (hpv : 0≤P.v parentp) (hps : 0≤P.s parentp)
    (hL : B.L≤1/(p*sourceLogCapacity b p))
    (hH : B.H≤1/sourceOddsCapacity b (sourceLogCapacity b p))
    (hhh : sourceExactH p≤B.hh) (hdd : 1-p≤B.dd)
    (hphi : B.phi≤sourcePhi lower b p)
    (hselection : B.selectionSlope*r+B.selectionIntercept≤selectionFraction (b/(1+b)) (p*r))
    (hlog : B.logLower≤sourceLogPenalty lower P.Dn P.ell p)
    (htau : B.tau*(d-1)≤P.tau p*(d-1)) :
    messageSourceEnvelope P B r d parentp≤messageSourceScalarRow P lower b p r d parentp := by
  have hsel := mul_le_mul_of_nonneg_left hselection (mul_nonneg hCJ hr0)
  have hvar := mul_le_mul_of_nonneg_left hdd (mul_nonneg hr0 (sq_nonneg d))
  have hpos := mul_le_mul_of_nonneg_right
    (mul_le_mul hu hL hL0 (hu0.trans hu)) (sq_nonneg (max 0 (1-d)))
  have hneg := mul_le_mul_of_nonneg_right
    (mul_le_mul hv hL hL0 (hv0.trans hv)) (sq_nonneg (max 0 (d-1)))
  have hposparent := mul_le_mul_of_nonneg_left hhh
    (mul_nonneg hpu (sq_nonneg (max 0 d)))
  have hnegparent := mul_le_mul_of_nonneg_left hhh
    (mul_nonneg hpv (sq_nonneg (max 0 (-d))))
  have hblock := mul_le_mul_of_nonneg_right
    (mul_le_mul hs hH hH0 (hs0.trans hs)) (mul_nonneg hr0 (sq_nonneg (1-d)))
  have hblockparent := mul_le_mul_of_nonneg_left hdd
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) hps) (sq_nonneg d))
  have hph := mul_le_mul_of_nonneg_left hphi (mul_nonneg hw hr0)
  have hflow := mul_le_mul_of_nonneg_left htau hr0
  unfold messageSourceEnvelope messageSourceScalarRow messageSourceMarkedRow messageSourceCore
  unfold sourceLogPenalty at hlog
  simp only [div_eq_mul_inv] at hsel hpos hneg hblock hlog ⊢
  nlinarith only [hsel,hvar,hpos,hneg,hposparent,hnegparent,hblock,hblockparent,hph,hflow,hlog]

#print axioms messageSourceEnvelope_le
end ForestUnimodality
