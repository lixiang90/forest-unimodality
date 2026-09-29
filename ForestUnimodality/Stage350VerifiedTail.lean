import ForestUnimodality.Stage350AffineTail
import ForestUnimodality.AffineTailRateCertificate

namespace ForestUnimodality.Stage350VerifiedTail

/-- Evidence for a particular real threshold and rate under the actual
row's distribution, including the chosen source's activity domain. -/
structure Verified (i : Fin 43) (alpha rate : ℝ) where
  source : Fin 15
  tilt : ℝ
  cap : (Stage350SourceTable.row i).b≤(AffineSourceLibrary.domain source).b
  alpha_nonneg : 0≤alpha
  tilt_nonneg : 0≤tilt
  rate_lower : rate≤Stage350SourceTable.affineTailRate i source alpha tilt

variable {V : Type*} [DecidableEq V]
theorem Verified.actual {i : Fin 43} {alpha rate : ℝ} (w : Verified i alpha rate)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 350≤S.card) (hlo : ((Stage350SourceTable.row i).a:ℝ)≤z)
    (hhi : z≤((Stage350SourceTable.row i).b:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableLowerTail G S B z (alpha*hardCoreAvailableMean G S B z)≤
      Real.exp (-rate*hardCoreAvailableMean G S B z) :=
  Stage350SourceTable.actual_affine_tail_le_rate i w.source hB hG hn hlo hhi hrank
    w.cap w.alpha_nonneg w.tilt_nonneg w.rate_lower

#print axioms Verified.actual
end ForestUnimodality.Stage350VerifiedTail
