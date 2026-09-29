import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 77
  A := (-2187184601428125632054389/2000000000000000000000000)
  B := (4069530303858268638350637/20000000000000000000000000)
  C := (1402140442788932350737241/2000000000000000000000000)
  dδ := (19070219007565927804570549/100000000000000000000000000)
  dM := (5394738636424738914554311/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(83488956638976130619766991/10000000000000000000000000), (6308219813386957142142819/250000000000000000000000)]
  retention := ![(3/5), (1/5)]
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
end ForestUnimodality.Stage80KernelData.Cell182
