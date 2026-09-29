import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 24
  A := (16398877900060427782236161/100000000000000000000000000)
  B := (35365629042754233302137123/1000000000000000000000000000)
  C := (-87922920323193654024152011/1000000000000000000000000000)
  dδ := (3884069709825338501119063/100000000000000000000000000)
  dM := (9405517342828267901566619/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2302721762406235939124599/2000000000000000000000000), (38194077284229779323254661/5000000000000000000000000)]
  retention := ![(3/5), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell014
