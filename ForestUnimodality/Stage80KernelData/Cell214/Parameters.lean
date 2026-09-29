import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 41
  A := (-1024907779178866263904979/1000000000000000000000000)
  B := (8225028388048882810323903/50000000000000000000000000)
  C := (6225384252343471036539313/20000000000000000000000000)
  dδ := (2025621235349129856118111/20000000000000000000000000)
  dM := (32766520968577727938864097/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(9204133640621529721670413/2000000000000000000000000), (2875148019499341955906857/250000000000000000000000)]
  retention := ![(7/20), (3/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/187)
  hi := (27/47)
  vmin := (540/2209)
  damping := (540/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell214
