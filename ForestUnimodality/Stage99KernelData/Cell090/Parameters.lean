import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-46043727040614961353526269/100000000000000000000000000)
  B := (85463188498669365178450619/1000000000000000000000000000)
  C := (36429329872375306419163277/10000000000000000000000000000)
  dδ := (47756240695604641743887697/500000000000000000000000000)
  dM := (14771994084291373023481997/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7529600423242599482875903/1000000000000000000000000), (20959051378973544643713467/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339/14214)
  hi := (107/207)
  vmin := (10700/42849)
  damping := (10700/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell090
