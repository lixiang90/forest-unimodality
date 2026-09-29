import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 58
  A := (19058083793626308001023517/100000000000000000000000000)
  B := (50391926690148344802899771/1000000000000000000000000000)
  C := (-14196471680379010946865259/5000000000000000000000000000)
  dδ := (21047837292637549405638353/250000000000000000000000000)
  dM := (11353984345987675646291043/12500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(21479035679324729457562171/5000000000000000000000000), (45120150505208815872038031/10000000000000000000000000), (4930141659671595277814049/100000000000000000000000)]
  retention := ![(4/5), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23/48)
  hi := (2983/6208)
  vmin := (575/2304)
  damping := (575/2304)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell043
