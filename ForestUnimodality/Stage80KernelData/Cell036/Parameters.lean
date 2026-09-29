import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (16057740702487441842194471/50000000000000000000000000)
  B := (51775709584813825459015391/1000000000000000000000000000)
  C := (-29957600074131166510704727/5000000000000000000000000000)
  dδ := (5255507212413355194735587/50000000000000000000000000)
  dM := (12613369655675203077210833/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63790097071982154730562797/10000000000000000000000000), (78990531885704760028943383/10000000000000000000000000), (24943983294047619381217373/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1687/3572)
  hi := (9/19)
  vmin := (3179995/12759184)
  damping := (3179995/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell036
