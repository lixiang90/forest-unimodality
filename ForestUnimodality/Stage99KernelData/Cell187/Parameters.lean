import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell187
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 16
  A := (5305214767365054151726511/25000000000000000000000000)
  B := (24063581001883653509576533/1000000000000000000000000000)
  C := (45907433179579786031165867/1000000000000000000000000000)
  dδ := (378733283163573339336061/12500000000000000000000000)
  dM := (28864904622310469687815337/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(15510481684326105078497449/10000000000000000000000000), (225662834504905429611199/62500000000000000000000)]
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
end ForestUnimodality.Stage99KernelData.Cell187
