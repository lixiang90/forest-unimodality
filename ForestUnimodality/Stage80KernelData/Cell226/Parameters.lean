import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell226
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 20
  A := (36298427948604636783969113/50000000000000000000000000)
  B := (4493930780180750012009483/250000000000000000000000000)
  C := (489826592351616907361489/4000000000000000000000000)
  dδ := (11717790967338520546903169/200000000000000000000000000)
  dM := (22134376012285594619542761/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(20700682181347081212141603/1000000000000000000000000000), (17820325135696637453008861/10000000000000000000000000), (3762392370400937657848317/625000000000000000000000)]
  retention := ![(9/10), (4/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236/371)
  hi := (9/14)
  vmin := (45/196)
  damping := (45/196)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell226
