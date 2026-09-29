import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 54
  A := (25690636415412463289698053/50000000000000000000000000)
  B := (41806686694701979123411917/1000000000000000000000000000)
  C := (-9149299410071730972310311/2500000000000000000000000000)
  dδ := (1778904477761227842513847/20000000000000000000000000)
  dM := (4537109168423550387139187/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(52668153427885844308775631/10000000000000000000000000), (19223976066635928283687917/10000000000000000000000000), (16744583863976474358281621/5000000000000000000000000), (8778081500390497637908993/200000000000000000000000)]
  retention := ![(4/5), (9/20), (2/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4487/9312)
  hi := (8999/18624)
  vmin := (21649775/86713344)
  damping := (21649775/86713344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell045
