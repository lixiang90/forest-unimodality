import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell231
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 16
  A := (31371845749572683182293531/50000000000000000000000000)
  B := (586370310659671371833479/50000000000000000000000000)
  C := (16214217646917972182052381/200000000000000000000000000)
  dδ := (46878685146472323652666603/1000000000000000000000000000)
  dM := (23437181438375591650997987/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(291641523747185482662303/50000000000000000000000)]
  retention := ![(7/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/3)
  hi := (35/52)
  vmin := (595/2704)
  damping := (1487500000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell231
