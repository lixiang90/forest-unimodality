import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 44
  A := (-5114595377912369517048319/5000000000000000000000000)
  B := (7233791296659557168435839/50000000000000000000000000)
  C := (14086296280959401117094387/50000000000000000000000000)
  dδ := (85630189704591200272609797/1000000000000000000000000000)
  dM := (12947049654142364378400787/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(28599684704406533874987417/5000000000000000000000000), (11814529051008131332878293/1000000000000000000000000)]
  retention := ![(2/5), (7/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/93)
  hi := (107/187)
  vmin := (8560/34969)
  damping := (8560/34969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell213
