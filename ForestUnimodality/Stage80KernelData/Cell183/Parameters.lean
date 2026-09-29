import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 78
  A := (-510563711083120504326871/400000000000000000000000)
  B := (19667474067190701680907239/100000000000000000000000000)
  C := (63144767266847123821094101/100000000000000000000000000)
  dδ := (8251673423656898098688117/50000000000000000000000000)
  dM := (9625245526849611401448703/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(45656231525462871445597557/5000000000000000000000000), (12412456840049209461085411/500000000000000000000000)]
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
end ForestUnimodality.Stage80KernelData.Cell183
