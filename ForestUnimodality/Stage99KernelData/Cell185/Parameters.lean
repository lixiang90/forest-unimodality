import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell185
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (9447741342226054717556849/50000000000000000000000000)
  B := (27046554129238675745483533/1000000000000000000000000000)
  C := (2182076933885459812945129/40000000000000000000000000)
  dδ := (8093469342049276760153731/250000000000000000000000000)
  dM := (34085010390698589803973317/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10424623845777931663292293/10000000000000000000000000), (2308634474622374366248323/500000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35/52)
  hi := (53/78)
  vmin := (1325/6084)
  damping := (13250000000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell185
