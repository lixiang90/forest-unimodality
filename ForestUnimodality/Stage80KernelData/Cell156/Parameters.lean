import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (1966928674781066133192553/10000000000000000000000000)
  B := (66616685398663499917404351/1000000000000000000000000000)
  C := (73880630268072702143689057/10000000000000000000000000000)
  dδ := (11973027464816048126561299/100000000000000000000000000)
  dM := (3234226448466473360227047/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(18380416828363279613256509/2500000000000000000000000), (3229308783064984922361873/125000000000000000000000), (14744309149977912198892227/2500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (15929/30104)
  hi := (95599/180624)
  vmin := (8128304975/32625029376)
  damping := (8128304975/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell156
