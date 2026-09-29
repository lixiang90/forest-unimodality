import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell282
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (53)
  A := (-17808312586253836283134433 / 200000000000000000000000000)
  B := (871377101754747668271861 / 40000000000000000000000000)
  C := (16136091525433091109498207 / 250000000000000000000000000)
  dδ := (3417084346250925247501229 / 200000000000000000000000000)
  dM := (13508643312121079932755507 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(48376584305148995213130547 / 10000000000000000000000000), (16780569107609728973784513 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 90)
  hi := (107 / 180)
  vmin := (7811 / 32400)
  damping := (7811 / 32400)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell282
