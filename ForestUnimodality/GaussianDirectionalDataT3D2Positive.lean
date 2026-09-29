import ForestUnimodality.GaussianDirectionalDataT3D2PositiveIdentity

import ForestUnimodality.GaussianDirectionalDataT3D2PositiveLeaf0

import ForestUnimodality.GaussianDirectionalDataT3D2PositiveLeaf1

import ForestUnimodality.GaussianDirectionalDataT3D2PositiveLeaf2

import ForestUnimodality.GaussianDirectionalDataT3D2PositiveLeaf3

import ForestUnimodality.GaussianDirectionalDataT3D2PositiveLeaf4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D2Positive

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.splitX (.splitY (.leaf cert0) (.leaf cert1)) (.leaf cert2)) (.leaf cert3)) (.leaf cert4)

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨⟨⟨leaf0_nonneg, leaf1_nonneg⟩, leaf2_nonneg⟩, leaf3_nonneg⟩, leaf4_nonneg⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by
  apply nonneg_of_compact terms 15 6 true degree_checked ?_ hx hy hy1
  intro u hu v hv
  rw [identity_semantic]
  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataT3D2Positive
