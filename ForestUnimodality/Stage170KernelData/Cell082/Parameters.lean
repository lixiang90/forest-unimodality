import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (67)
  A := (22995043030171946067952149 / 500000000000000000000000000)
  B := (2628487311451499670866827 / 250000000000000000000000000)
  C := (-38076385297939767393682331 / 1000000000000000000000000000)
  dδ := (92699259168109345019548329 / 10000000000000000000000000000)
  dM := (989827260333800552471583 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(40390439196048655290383067 / 5000000000000000000000000), (9754400614876754360693667 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103 / 255)
  hi := (7 / 17)
  vmin := (15656 / 65025)
  damping := (15656 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell082
