import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (174)
  A := (-733533769306315053810863 / 500000000000000000000000)
  B := (1145717750553686964387623 / 20000000000000000000000000)
  C := (12312174489284059505402047 / 50000000000000000000000000000)
  dδ := (9586875089979469966028347 / 250000000000000000000000000)
  dM := (38036154540572320167587939 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(203919006901002342058149 / 15625000000000000000000), (637776099051412188600807 / 4000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell154
