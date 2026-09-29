import ForestUnimodality.GaussianDirectionalDataHalfZeroIdentity

import ForestUnimodality.GaussianDirectionalDataHalfZeroLeaf0

import ForestUnimodality.GaussianDirectionalDataHalfZeroLeaf1

import ForestUnimodality.GaussianDirectionalDataHalfZeroLeaf2

import ForestUnimodality.GaussianDirectionalDataHalfZeroLeaf3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataHalfZero

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.splitX (.leaf cert0) (.leaf cert1)) (.leaf cert2)) (.leaf cert3)

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨⟨leaf0_nonneg, leaf1_nonneg⟩, leaf2_nonneg⟩, leaf3_nonneg⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)

    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by

  apply nonneg_of_compact terms 13 8 true degree_checked ?_ hx hy hy1

  intro u hu v hv

  rw [identity_semantic]

  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)

#print axioms identity_semantic
#print axioms cover_checked
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataHalfZero
