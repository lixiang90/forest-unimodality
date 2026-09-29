import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 82
  A := (36744021664306154463019993/100000000000000000000000000)
  B := (89834502899754309357405191/1000000000000000000000000000)
  C := (-31488058279781461212820659/50000000000000000000000000)
  dδ := (7975809264906773277115093/50000000000000000000000000)
  dM := (4014305468046962428740887/2000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(79166158137151594331726301/10000000000000000000000000), (14465247925923259142422239/5000000000000000000000000), (6699458666609150903070713/250000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17/37)
  hi := (1613/3478)
  vmin := (340/1369)
  damping := (340/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell028
