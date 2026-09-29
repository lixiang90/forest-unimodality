import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell187
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18875253472541124077821451/10000000000000000000000000)
  B := (6718234267169831408494929/50000000000000000000000000)
  C := (59492827341504237945168931/10000000000000000000000000000)
  dδ := (7579153939241198290055479/100000000000000000000000000)
  dM := (17316331706407905605821229/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15556655509309372575899033/1000000000000000000000000), (50485986886778249527196749/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95749/180624)
  hi := (47887/90312)
  vmin := (2031605975/8156257344)
  damping := (2031605975/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell187
