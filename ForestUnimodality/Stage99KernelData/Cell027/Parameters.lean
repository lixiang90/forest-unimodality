import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 79
  A := (-15280427904272672112284681/50000000000000000000000000)
  B := (41765323011797202135131357/500000000000000000000000000)
  C := (-41745260813176460201745499/100000000000000000000000000)
  dδ := (97145159963328009400385099/1000000000000000000000000000)
  dM := (1585143119413589271951559/1250000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(539186401130656856039991/78125000000000000000000), (28575515036644347333094629/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301/666)
  hi := (17/37)
  vmin := (109865/443556)
  damping := (109865/443556)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell027
