import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 51
  A := (-3396709791223173296970117/5000000000000000000000000)
  B := (756968249475444499019261/8000000000000000000000000)
  C := (4360094747757250338571211/1000000000000000000000000000)
  dδ := (9170060958862667754853959/100000000000000000000000000)
  dM := (3901658391640081273606111/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7309047651305806247989949/1000000000000000000000000), (1341383746112771113701001/31250000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/52)
  hi := (22597/43472)
  vmin := (471712375/1889814784)
  damping := (471712375/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell100
