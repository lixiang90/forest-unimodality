import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell375
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (87)
  A := (-17657588084056450888681411 / 25000000000000000000000000)
  B := (53599817094866310240863783 / 1000000000000000000000000000)
  C := (-19927219334315335319551821 / 100000000000000000000000000)
  dδ := (39531640045165544750105369 / 1000000000000000000000000000)
  dM := (44741599713009442022479401 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(93878077088138116579330017 / 10000000000000000000000000), (28986914754255433734897451 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4 / 9)
  hi := (301 / 666)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell375
