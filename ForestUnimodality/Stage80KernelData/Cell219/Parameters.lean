import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 31
  A := (24370635044340618991043357/10000000000000000000000000)
  B := (-18523418290087030613211283/500000000000000000000000000)
  C := (10950103442456292357487513/50000000000000000000000000)
  dδ := (8139972404524696558691943/100000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(20846599483954579845601529/10000000000000000000000000), (11135534790134642424419553/5000000000000000000000000), (54901166768313682808866361/10000000000000000000000000), (24535051752540595337848117/5000000000000000000000000)]
  retention := ![(9/10), (4/5), (3/20), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell219
