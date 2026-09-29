import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18753212592064555830262407/10000000000000000000000000)
  B := (2654685155197200607801733/20000000000000000000000000)
  C := (58244581128960451824050359/10000000000000000000000000000)
  dδ := (7486811199785965709185831/100000000000000000000000000)
  dM := (1701046354128515035453173/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7767645039278932017623447/500000000000000000000000), (50520355008348133196705021/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95599/180624)
  hi := (11953/22578)
  vmin := (127000625/509766084)
  damping := (127000625/509766084)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell169
