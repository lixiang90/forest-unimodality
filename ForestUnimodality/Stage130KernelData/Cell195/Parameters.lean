import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell195
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 77
  A := (-14631658093199592551769683/10000000000000000000000000)
  B := (5158645428596386056652179/50000000000000000000000000)
  C := (10099774769673098423483637/2000000000000000000000000000)
  dδ := (68716781126853018757394409/1000000000000000000000000000)
  dM := (763375367804071353972431/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5010649932314941601418923/500000000000000000000000), (22879416998567512209206143/10000000000000000000000000), (1010194897169400363168279/62500000000000000000000), (11750204344435239534050197/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113/213)
  hi := (8069/15194)
  vmin := (57491625/230857636)
  damping := (57491625/230857636)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell195
