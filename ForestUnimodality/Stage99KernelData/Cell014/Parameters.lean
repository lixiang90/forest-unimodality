import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 27
  A := (26974683500816066695549011/100000000000000000000000000)
  B := (4932866702077469238385543/250000000000000000000000000)
  C := (-30689978542522936000302991/500000000000000000000000000)
  dδ := (6428559506993232475213773/250000000000000000000000000)
  dM := (4729541094126841387426663/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(3336682480992537169761647/2500000000000000000000000), (43475242355131937799228581/5000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (91/255)
  hi := (31/85)
  vmin := (14924/65025)
  damping := (14924/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell014
