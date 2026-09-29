import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-13046832949683172986254931/10000000000000000000000000)
  B := (3364693843455267285857957/25000000000000000000000000)
  C := (-26807402283094694528386981/5000000000000000000000000000)
  dδ := (477910092733389857411197/5000000000000000000000000)
  dM := (4437234416021057850643139/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(74788576747262567323559779/10000000000000000000000000), (40126248492228661746139551/1000000000000000000000000)]
  retention := ![(3/5), (1/20)]
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
end ForestUnimodality.Stage99KernelData.Cell036
