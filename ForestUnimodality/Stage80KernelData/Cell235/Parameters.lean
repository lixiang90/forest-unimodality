import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell235
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 14
  A := (10171290579143946941798049/20000000000000000000000000)
  B := (8435796075914681405039097/500000000000000000000000000)
  C := (68399430412655545796773993/1000000000000000000000000000)
  dδ := (5727428779643291452405851/125000000000000000000000000)
  dM := (5909573452304248955199717/20000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(34956549717003264632353421/10000000000000000000000000), (12961365940378402061838869/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/156)
  hi := (9/13)
  vmin := (36/169)
  damping := (1440000000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell235
