import ForestUnimodality.GaussianDirectionalDataT3D2NegativeIdentity

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf0

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf1

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf2

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf3

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf4

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf5

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf6

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf7

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf8

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf9

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf10

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf11

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf12

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf13

import ForestUnimodality.GaussianDirectionalDataT3D2NegativeLeaf14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D2Negative

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.splitX (.leaf cert0) (.splitY (.splitX (.leaf cert1) (.leaf cert2)) (.splitX (.leaf cert3) (.leaf cert4)))) (.splitX (.splitY (.splitX (.leaf cert5) (.splitY (.leaf cert6) (.leaf cert7))) (.leaf cert8)) (.splitY (.splitX (.splitY (.leaf cert9) (.leaf cert10)) (.leaf cert11)) (.leaf cert12)))) (.splitY (.leaf cert13) (.leaf cert14))

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨⟨leaf0_nonneg, ⟨⟨leaf1_nonneg, leaf2_nonneg⟩, ⟨leaf3_nonneg, leaf4_nonneg⟩⟩⟩, ⟨⟨⟨leaf5_nonneg, ⟨leaf6_nonneg, leaf7_nonneg⟩⟩, leaf8_nonneg⟩, ⟨⟨⟨leaf9_nonneg, leaf10_nonneg⟩, leaf11_nonneg⟩, leaf12_nonneg⟩⟩⟩, ⟨leaf13_nonneg, leaf14_nonneg⟩⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by
  apply nonneg_of_compact terms 13 8 true degree_checked ?_ hx hy hy1
  intro u hu v hv
  rw [identity_semantic]
  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataT3D2Negative
