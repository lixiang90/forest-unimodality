import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell316
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (40)
  A := (38656893433595828639681713 / 500000000000000000000000000)
  B := (3123866607531593057867081 / 250000000000000000000000000)
  C := (5787045034556686368132361 / 200000000000000000000000000)
  dδ := (1331463694733544525158897 / 125000000000000000000000000)
  dM := (2378624391078643345986271 / 40000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(51063090440122138602419 / 10000000000000000000000), (48781128258950472442734281 / 5000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467 / 742)
  hi := (236 / 371)
  vmin := (31860 / 137641)
  damping := (31860 / 137641)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell316
