import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell211
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (167)
  A := (-13334348664271732831565487 / 10000000000000000000000000)
  B := (4520058497145826997831719 / 100000000000000000000000000)
  C := (18607124980068454056514327 / 100000000000000000000000000)
  dδ := (103810778987568630427063 / 4000000000000000000000000)
  dM := (22924336947286748952627711 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2976046937521556134953471 / 125000000000000000000000), (10536711773284582704945933 / 200000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell211
