import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 76
  A := (-5135084009933332477260137/5000000000000000000000000)
  B := (91354567804557501586870671/1000000000000000000000000000)
  C := (26375197076261147621778491/100000000000000000000000000)
  dδ := (29548155910433211018828459/500000000000000000000000000)
  dM := (5167312373547304710577621/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(35062912159943304679643461/5000000000000000000000000), (6448716463557983225030057/250000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/89)
  hi := (99/179)
  vmin := (7920/32041)
  damping := (7920/32041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell216
