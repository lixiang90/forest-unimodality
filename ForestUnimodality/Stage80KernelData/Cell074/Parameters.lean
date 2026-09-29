import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 36
  A := (18978345554296428099405603/10000000000000000000000000)
  B := (-1537376882152811756465649/125000000000000000000000000)
  C := (-84973654403904560865334883/100000000000000000000000000000)
  dδ := (11671111949398293994306641/100000000000000000000000000)
  dM := (68783306403466819203135207/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(46333512015526497063167/7812500000000000000000), (15925646817246366993003903/500000000000000000000000)]
  retention := ![(4/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3193/6468)
  hi := (49/99)
  vmin := (10457075/41835024)
  damping := (10457075/41835024)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell074
