import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-80103589111682132028136039/100000000000000000000000000)
  B := (10158697685006287669828851/100000000000000000000000000)
  C := (365874665916108773866533/80000000000000000000000000)
  dδ := (45733979044041431216705007/500000000000000000000000000)
  dM := (16637014118476270343321977/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(65016027409763719191460041/10000000000000000000000000), (1002738326494693410495529/1000000000000000000000000), (42607738516647962967454077/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
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
end ForestUnimodality.Stage99KernelData.Cell104
