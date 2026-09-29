import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-3373413459189438114975701/2000000000000000000000000)
  B := (11459145987048795223284259/100000000000000000000000000)
  C := (6292806188323068691814477/1250000000000000000000000000)
  dδ := (35048205292031432700472493/500000000000000000000000000)
  dM := (2728793158671790307356897/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(28386020418234512163735417/5000000000000000000000000), (81369377469947590242327351/10000000000000000000000000), (6043409927413244275840043/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94503/178928)
  hi := (28/53)
  vmin := (700/2809)
  damping := (700/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell146
