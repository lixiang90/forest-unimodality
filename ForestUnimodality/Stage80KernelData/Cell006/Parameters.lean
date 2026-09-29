import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (24801095637494839927228441/1000000000000000000000000000)
  B := (30357266988684433739464907/1000000000000000000000000000)
  C := (-8309557723111378468860977/200000000000000000000000000)
  dδ := (26526640519434790954633741/1000000000000000000000000000)
  dM := (31873528449153487986447719/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(30961054810831858258302063/1000000000000000000000000000), (25263798693378984872026649/5000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/126)
  hi := (19/63)
  vmin := (3293/15876)
  damping := (32930000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell006
