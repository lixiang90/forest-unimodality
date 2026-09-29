import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 21
  A := (48419706163148645288174521/500000000000000000000000000)
  B := (20189962547975535273048209/1000000000000000000000000000)
  C := (-16827382630956636000441051/500000000000000000000000000)
  dδ := (19196756473267562875806291/1000000000000000000000000000)
  dM := (3244992526284210150600007/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(26882710551603911097728883/50000000000000000000000000), (61730103462258423263619989/10000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/42)
  hi := (20/63)
  vmin := (377/1764)
  damping := (3770000000000000000000000000000000000000000/43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell008
