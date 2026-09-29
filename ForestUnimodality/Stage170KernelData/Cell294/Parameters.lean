import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell294
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (41)
  A := (-42868213677055001511462251 / 1000000000000000000000000000)
  B := (13421380172353582910238501 / 500000000000000000000000000)
  C := (68397892256276002220793941 / 1000000000000000000000000000)
  dδ := (4381281869381904031657271 / 200000000000000000000000000)
  dM := (5213943005776169029768033 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(4006118238175014667490359 / 250000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell294
