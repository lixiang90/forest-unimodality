import ForestUnimodality.GaussianDirectionalDataT1PositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT1Positive

open PolynomialList BernsteinCertificate RationalCompactification

theorem identity_semantic (u v : ℝ) :
    evalReal₂ (compactPolynomial terms 15 6 true) u v = evalReal₂ compact u v := by
  rw [eval_compactPolynomial]
  norm_num [terms, compact, evalReal₂, eval, evalList, liftEvaluation, rationalEvaluation]
  ring
#print axioms identity_semantic

end ForestUnimodality.GaussianDirectionalDataT1Positive
