import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 60
  A := (-1105141797013827165474531/1562500000000000000000000)
  B := (40841027183577308101725123/500000000000000000000000000)
  C := (20705938846461852120839353/5000000000000000000000000000)
  dδ := (78142335108228044848743821/1000000000000000000000000000)
  dM := (11660117537779200735936769/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(57159169675566789958764957/100000000000000000000000000), (41885656073237598207015253/5000000000000000000000000), (12489761072663089436218797/1000000000000000000000000), (9445058529626480847696257/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531/2926)
  hi := (11/21)
  vmin := (110/441)
  damping := (110/441)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell115
