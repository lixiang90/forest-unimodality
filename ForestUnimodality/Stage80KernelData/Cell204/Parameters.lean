import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell204
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 45
  A := (-5333665611499707975795559/5000000000000000000000000)
  B := (15380739118418479405292487/100000000000000000000000000)
  C := (31317346991277772438877491/100000000000000000000000000)
  dδ := (18990455557404745112748401/200000000000000000000000000)
  dM := (14282898541224302389057721/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(37034099189872526913802631/10000000000000000000000000), (575478344092694342748473/40000000000000000000000)]
  retention := ![(2/5), (7/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell204
