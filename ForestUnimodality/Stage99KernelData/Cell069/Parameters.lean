import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 63
  A := (-92404447484328160577149447/100000000000000000000000000)
  B := (89527731738027568897386743/1000000000000000000000000000)
  C := (6288268524255822417012851/5000000000000000000000000000)
  dδ := (15291071466217304175572167/200000000000000000000000000)
  dM := (488357628323146664151011/400000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5150474534655745673106253/625000000000000000000000), (26880004283037251866517181/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51/101)
  hi := (10429/20604)
  vmin := (106115075/424524816)
  damping := (106115075/424524816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell069
