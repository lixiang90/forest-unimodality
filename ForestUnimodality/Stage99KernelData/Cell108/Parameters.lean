import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 51
  A := (-35723410215758302276967129/50000000000000000000000000)
  B := (97136913759144766222775047/1000000000000000000000000000)
  C := (46467357501581334558449221/10000000000000000000000000000)
  dδ := (92102215926057953709893411/1000000000000000000000000000)
  dM := (4013070453915240339351489/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(73126116563317307139868717/10000000000000000000000000), (42885474659177205580817827/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell108
