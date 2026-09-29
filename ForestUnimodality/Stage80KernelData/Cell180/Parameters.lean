import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 81
  A := (-179932195531395656451501/156250000000000000000000)
  B := (18590759457001121424113421/100000000000000000000000000)
  C := (13066609007087515159639679/20000000000000000000000000)
  dδ := (16924048562468038681139149/100000000000000000000000000)
  dM := (17963769017015447301832687/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(1032118523460406578351467/100000000000000000000000), (6301171944503984434504673/250000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/54)
  hi := (2557/4752)
  vmin := (5612615/22581504)
  damping := (5612615/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell180
