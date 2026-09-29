import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 34
  A := (19861455377694386503861779/10000000000000000000000000)
  B := (-21410925186305169998224329/1000000000000000000000000000)
  C := (15063324240511166696165901/100000000000000000000000000)
  dδ := (25344586931076596575396209/500000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(1232131613316638762967159/400000000000000000000000), (1046134424511761112919217/5000000000000000000000000), (10262776831428765955678273/10000000000000000000000000), (5628944204527125627635087/500000000000000000000000)]
  retention := ![(9/10), (7/10), (3/5), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/180)
  hi := (3/5)
  vmin := (6/25)
  damping := (6/25)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell173
