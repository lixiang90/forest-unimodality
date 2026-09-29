import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (1276953288761346225221871/2500000000000000000000000)
  B := (730420277494810143981141/40000000000000000000000000)
  C := (78701452387859013870574643/1000000000000000000000000000)
  dδ := (45173184016710610233502621/1000000000000000000000000000)
  dM := (30093046106808093867815423/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(43275073787023474736201933/10000000000000000000000000), (4315189917660817164879461/2500000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/3)
  hi := (35/52)
  vmin := (595/2704)
  damping := (1487500000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell232
