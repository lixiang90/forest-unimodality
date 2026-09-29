import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (83)
  A := (-10609349243386570620373277 / 125000000000000000000000000)
  B := (16379998552804884981437539 / 1000000000000000000000000000)
  C := (-34203382800191722834526331 / 500000000000000000000000000)
  dδ := (14011510783521991668765239 / 1000000000000000000000000000)
  dM := (2961949721785357030924557 / 40000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(84444129995251469011918743 / 10000000000000000000000000), (27192225498771307456991053 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell095
