import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 59
  A := (-3123076039888904978347739/2500000000000000000000000)
  B := (11407808976302523384926957/100000000000000000000000000)
  C := (-26687077876391706622583033/5000000000000000000000000000)
  dδ := (3368900042122556226509289/40000000000000000000000000)
  dM := (16404156193756051600185497/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13392327291385424103964397/10000000000000000000000000), (5640949638965496726328297/625000000000000000000000), (2956696396692669370764861/62500000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1733/3648)
  hi := (869/1824)
  vmin := (3318695/13307904)
  damping := (3318695/13307904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell037
