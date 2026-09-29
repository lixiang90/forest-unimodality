import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-1863813620358848650848671/1250000000000000000000000)
  B := (10914349589192817724381257/100000000000000000000000000)
  C := (35287448331066599387095817/10000000000000000000000000000)
  dδ := (14431136183528400773745659/200000000000000000000000000)
  dM := (6716414185558120279392891/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2142369233509540116244807/312500000000000000000000), (3309159830200872343120011/625000000000000000000000), (5887704579305590851801/97656250000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311/21736)
  hi := (22647/43472)
  vmin := (471623775/1889814784)
  damping := (471623775/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell109
