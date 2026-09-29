import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 30
  A := (20490221399767928224022739/100000000000000000000000000)
  B := (24094356005636290846139147/1000000000000000000000000000)
  C := (-18819570811565756313088471/250000000000000000000000000)
  dδ := (14162501280243836032646243/500000000000000000000000000)
  dM := (12298873897361210175832591/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(977615028976929339998847/625000000000000000000000), (24872223969275459865002631/2500000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/51)
  hi := (97/255)
  vmin := (608/2601)
  damping := (608/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell016
