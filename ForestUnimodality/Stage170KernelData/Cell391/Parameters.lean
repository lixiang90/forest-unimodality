import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell391
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (114)
  A := (-9370411330879410921568251 / 5000000000000000000000000)
  B := (23096561615927234389911149 / 250000000000000000000000000)
  C := (7234975761980829821878869 / 2500000000000000000000000000)
  dδ := (10479350330189288187376917 / 200000000000000000000000000)
  dM := (41380662080875186019032763 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(17462450647555236571406567 / 1000000000000000000000000), (94613974324922722303199407 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109 / 209)
  hi := (11 / 21)
  vmin := (110 / 441)
  damping := (110 / 441)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell391
