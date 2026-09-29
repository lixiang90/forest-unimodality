import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (196)
  A := (-4067824195961957492428951 / 2500000000000000000000000)
  B := (28434253844530767846299213 / 500000000000000000000000000)
  C := (-1435659686476688798664747 / 1000000000000000000000000000)
  dδ := (35210438648660115357191813 / 1000000000000000000000000000)
  dM := (34990278757897976024196507 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3638064478587622829763859 / 250000000000000000000000), (17978684762830258137000783 / 100000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23 / 48)
  hi := (47 / 97)
  vmin := (575 / 2304)
  damping := (575 / 2304)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell135
