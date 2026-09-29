import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 78
  A := (-158044634357696936604043/125000000000000000000000)
  B := (95776314497160286443033783/1000000000000000000000000000)
  C := (-2685102680028040472194617/625000000000000000000000000)
  dδ := (1780578705375185019632589/25000000000000000000000000)
  dM := (5717732511052512050370167/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(38994689957214658804218743/5000000000000000000000000), (12035753763067145172271921/5000000000000000000000000), (332313185985764789620589/5000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1733/3648)
  hi := (869/1824)
  vmin := (3318695/13307904)
  damping := (3318695/13307904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell035
