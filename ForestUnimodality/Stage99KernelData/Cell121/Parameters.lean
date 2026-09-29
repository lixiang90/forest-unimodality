import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 60
  A := (-45677637980177395792935613/50000000000000000000000000)
  B := (1841906884297619118040501/20000000000000000000000000)
  C := (6033393154996614894322593/1250000000000000000000000000)
  dδ := (39394665072143876527466233/500000000000000000000000000)
  dM := (203210018407413222046691/156250000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(53040518197523790766556573/1000000000000000000000000000), (86411114369661206069395121/10000000000000000000000000), (25159171334804209863023061/500000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell121
