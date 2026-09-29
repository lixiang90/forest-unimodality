import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-26748997888003830436076669/50000000000000000000000000)
  B := (58772353156528830964155929/1000000000000000000000000000)
  C := (-10089726107442519020818139/50000000000000000000000000)
  dδ := (45290710183181842607424983/1000000000000000000000000000)
  dM := (59843666175363565470218807/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(25883197974974652133539621/5000000000000000000000000), (4941594376315924819209613/200000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67/153)
  hi := (4/9)
  vmin := (5762/23409)
  damping := (5762/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell025
