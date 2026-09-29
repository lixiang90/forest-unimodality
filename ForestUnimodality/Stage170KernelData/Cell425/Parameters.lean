import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell425
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (22)
  A := (6458065334312380001868803 / 50000000000000000000000000)
  B := (18260120485898839737259891 / 1000000000000000000000000000)
  C := (16047984651059263305761249 / 500000000000000000000000000)
  dδ := (18089532904357250725491113 / 1000000000000000000000000000)
  dM := (7237715600747663291947981 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(34438304226919909112325513 / 5000000000000000000000000), (38363265140348179471629919 / 100000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35 / 52)
  hi := (53 / 78)
  vmin := (1325 / 6084)
  damping := (13250000000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell425
