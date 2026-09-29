import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (4330522943628024055158221/2000000000000000000000000)
  B := (-5369485551494052738563667/200000000000000000000000000)
  C := (-2035177200042492980103237/1000000000000000000000000000)
  dδ := (5758335802899302441337781/50000000000000000000000000)
  dM := (859607241834345922430749/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(65618221620762904322532449/10000000000000000000000000), (11981152783547935669616891/1000000000000000000000000), (5377291246832961668644657/250000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24/49)
  hi := (9529/19404)
  vmin := (600/2401)
  damping := (600/2401)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell067
