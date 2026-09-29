import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell223
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 24
  A := (21991874326705081566046829/10000000000000000000000000)
  B := (-31330198709005767365720629/1000000000000000000000000000)
  C := (126259761213246513023023/800000000000000000000000)
  dδ := (13499831274827506222280249/200000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(5079821150301167875795727/2000000000000000000000000), (3127453106335099652923759/2500000000000000000000000), (18813464791531420150505483/10000000000000000000000000), (2744119074377679545762021/500000000000000000000000)]
  retention := ![(9/10), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129/209)
  hi := (33/53)
  vmin := (660/2809)
  damping := (660/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell223
