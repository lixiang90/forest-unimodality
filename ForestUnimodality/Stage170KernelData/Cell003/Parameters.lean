import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (1835810259765531904463387 / 10000000000000000000000000)
  B := (37426264736576926941968857 / 5000000000000000000000000000)
  C := (-2884888106299238023921827 / 250000000000000000000000000)
  dδ := (88131015825255350215616801 / 10000000000000000000000000000)
  dM := (5755903579855354818114923 / 250000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(94999974850933347170212073 / 100000000000000000000000)]
  retention := ![(9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 4)
  hi := (9 / 35)
  vmin := (3 / 16)
  damping := (7500000000000000000000000000000000000000 / 98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell003
