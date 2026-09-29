import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell221
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 27
  A := (-6999059392242013561968861/500000000000000000000000000)
  B := (72271646397969249719928087/1000000000000000000000000000)
  C := (2248494214356784245967269/12500000000000000000000000)
  dδ := (70749420065369703070068397/1000000000000000000000000000)
  dM := (6949444815160599545067477/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(1123362206688894443518123/625000000000000000000000), (42891987409846610290742319/5000000000000000000000000)]
  retention := ![(7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123/203)
  hi := (63/103)
  vmin := (2520/10609)
  damping := (2520/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell221
