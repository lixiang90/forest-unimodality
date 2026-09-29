import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell196
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-529562582813080086685531/312500000000000000000000)
  B := (639878176895490851511239/6250000000000000000000000)
  C := (46494063976332527382551163/10000000000000000000000000000)
  dδ := (30859526059989799556815271/500000000000000000000000000)
  dM := (10924731122792723063408271/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(176822094866017603953523/15625000000000000000000), (4852743694157598319804947/2000000000000000000000000), (36252677085384945598889317/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113/213)
  hi := (8069/15194)
  vmin := (57491625/230857636)
  damping := (57491625/230857636)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell196
