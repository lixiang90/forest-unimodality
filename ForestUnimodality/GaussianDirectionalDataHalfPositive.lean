import ForestUnimodality.GaussianDirectionalDataHalfPositiveIdentity

import ForestUnimodality.GaussianDirectionalDataHalfPositiveLeaf0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataHalfPositive

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .leaf cert0

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact leaf0_nonneg

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)

    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by

  apply nonneg_of_compact terms 15 6 true degree_checked ?_ hx hy hy1

  intro u hu v hv

  rw [identity_semantic]

  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)

#print axioms identity_semantic
#print axioms cover_checked
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataHalfPositive
