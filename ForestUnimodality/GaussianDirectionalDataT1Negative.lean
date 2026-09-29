import ForestUnimodality.GaussianDirectionalDataT1NegativeIdentity

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf0

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf1

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf2

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf3

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf4

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf5

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf6

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf7

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf8

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf9

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf10

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf11

import ForestUnimodality.GaussianDirectionalDataT1NegativeLeaf12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT1Negative

open PolynomialList BernsteinCertificate RationalCompactification

def cover : Cover := .splitX (.splitY (.splitX (.leaf cert0) (.splitY (.splitX (.leaf cert1) (.leaf cert2)) (.splitX (.leaf cert3) (.leaf cert4)))) (.splitX (.splitY (.splitX (.leaf cert5) (.splitY (.leaf cert6) (.leaf cert7))) (.leaf cert8)) (.splitY (.leaf cert9) (.leaf cert10)))) (.splitY (.leaf cert11) (.leaf cert12))

theorem cover_checked : cover.Semantic compact 0 1 0 1 := by
  simp only [cover, Cover.Semantic]
  norm_num only
  exact ⟨⟨⟨leaf0_nonneg, ⟨⟨leaf1_nonneg, leaf2_nonneg⟩, ⟨leaf3_nonneg, leaf4_nonneg⟩⟩⟩, ⟨⟨⟨leaf5_nonneg, ⟨leaf6_nonneg, leaf7_nonneg⟩⟩, leaf8_nonneg⟩, ⟨leaf9_nonneg, leaf10_nonneg⟩⟩⟩, ⟨leaf11_nonneg, leaf12_nonneg⟩⟩

theorem region_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy1 : true = false → y ≤ 1) : 0 ≤ evalSparse terms x y := by
  apply nonneg_of_compact terms 13 8 true degree_checked ?_ hx hy hy1
  intro u hu v hv
  rw [identity_semantic]
  exact Cover.Semantic.sound cover cover_checked (by simpa using hu) (by simpa using hv)
#print axioms region_nonneg

end ForestUnimodality.GaussianDirectionalDataT1Negative
