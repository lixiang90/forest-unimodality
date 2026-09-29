import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (2175241748349055051603429 / 12500000000000000000000000)
  B := (91444822098207638461087043 / 10000000000000000000000000000)
  C := (-3356976201862324482583233 / 100000000000000000000000000)
  dδ := (962662189136700811864511 / 100000000000000000000000000)
  dM := (35242260324445741945069421 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(33780132037790435717283799 / 5000000000000000000000000), (319025542732726741235183 / 20000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 85)
  hi := (101 / 255)
  vmin := (1716 / 7225)
  damping := (1716 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell074
