import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 42
  A := (-15607037914426563904868317/250000000000000000000000000)
  B := (76279562826177635392888021/1000000000000000000000000000)
  C := (8525501885897483408949249/2000000000000000000000000000)
  dδ := (1108366968265951102434741/10000000000000000000000000)
  dM := (16228728235469496322257443/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(70900548307943420667243117/10000000000000000000000000), (34740953071660932494069129/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311/21736)
  hi := (22647/43472)
  vmin := (471623775/1889814784)
  damping := (471623775/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell116
