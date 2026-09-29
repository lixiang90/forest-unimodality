import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-9152536373353964985088993/12500000000000000000000000)
  B := (95797063010119129500274937/1000000000000000000000000000)
  C := (11762102984953123050761159/12500000000000000000000000000)
  dδ := (90964579404272868923264639/1000000000000000000000000000)
  dM := (7789869291209515749646597/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(43890569466763329486980183/10000000000000000000000000), (21706783377910765509000157/5000000000000000000000000), (4144736985670772355661029/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10429/20604)
  hi := (5227/10302)
  vmin := (26527025/106131204)
  damping := (26527025/106131204)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell070
