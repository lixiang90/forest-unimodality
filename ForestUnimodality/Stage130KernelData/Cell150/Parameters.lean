import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-15956216817142720343269957/10000000000000000000000000)
  B := (49498404566631001855192551/500000000000000000000000000)
  C := (1830616497637597636649609/400000000000000000000000000)
  dδ := (12597206521176187998811713/200000000000000000000000000)
  dM := (2121630236135356277482611/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2413704800631633773377871/200000000000000000000000), (1991364145660242668256501/1250000000000000000000000), (15304664425173328368146031/1000000000000000000000000), (57379699082064249182622007/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28/53)
  hi := (95449/180624)
  vmin := (8129868575/32625029376)
  damping := (8129868575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell150
