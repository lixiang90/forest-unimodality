import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (78)
  A := (-21690334809718296970260099 / 100000000000000000000000000)
  B := (21209201840710945746737437 / 1000000000000000000000000000)
  C := (-76826266532145262577735423 / 1000000000000000000000000000)
  dδ := (3225223977760607180220731 / 200000000000000000000000000)
  dM := (5404726532623801017306969 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(8551930408525008076026097 / 250000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65 / 153)
  hi := (22 / 51)
  vmin := (5720 / 23409)
  damping := (5720 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell094
