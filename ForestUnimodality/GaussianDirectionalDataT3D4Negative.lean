import ForestUnimodality.GaussianDirectionalDataT3D4NegativeIdentity

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf0

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf1

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf2

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf3

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf4

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf5

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf6

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf7

import ForestUnimodality.GaussianDirectionalDataT3D4NegativeLeaf8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D4Negative

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.splitX (.leaf cert0) (.splitY (.leaf cert1) (.leaf cert2))) (.splitX (.splitY (.splitX (.leaf cert3) (.leaf cert4)) (.leaf cert5)) (.leaf cert6))) (.splitY (.leaf cert7) (.leaf cert8))

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨⟨leaf0_nonneg, ⟨leaf1_nonneg, leaf2_nonneg⟩⟩, ⟨⟨⟨leaf3_nonneg, leaf4_nonneg⟩, leaf5_nonneg⟩, leaf6_nonneg⟩⟩, ⟨leaf7_nonneg, leaf8_nonneg⟩⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by
  apply nonneg_of_compact terms 13 8 true degree_checked ?_ hx hy hy1
  intro u hu v hv
  rw [identity_semantic]
  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataT3D4Negative
