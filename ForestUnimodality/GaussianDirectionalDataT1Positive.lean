import ForestUnimodality.GaussianDirectionalDataT1PositiveIdentity

import ForestUnimodality.GaussianDirectionalDataT1PositiveLeaf0

import ForestUnimodality.GaussianDirectionalDataT1PositiveLeaf1

import ForestUnimodality.GaussianDirectionalDataT1PositiveLeaf2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT1Positive

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.leaf cert0) (.leaf cert1)) (.leaf cert2)

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨leaf0_nonneg, leaf1_nonneg⟩, leaf2_nonneg⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by
  apply nonneg_of_compact terms 15 6 true degree_checked ?_ hx hy hy1
  intro u hu v hv
  rw [identity_semantic]
  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataT1Positive
