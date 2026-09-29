import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell184
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 79
  A := (-2780224098187455808428581/2500000000000000000000000)
  B := (9135261336095133744006347/50000000000000000000000000)
  C := (2540788562259330252146583/4000000000000000000000000)
  dδ := (4141816096023506060808117/25000000000000000000000000)
  dM := (35382816712945801447542937/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(2561632268300110037984041/250000000000000000000000), (2831630554380173858675107/250000000000000000000000), (6502475232024644391515267/500000000000000000000000)]
  retention := ![(3/5), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2557/4752)
  hi := (427/792)
  vmin := (155855/627264)
  damping := (155855/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell184
