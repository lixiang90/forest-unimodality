import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell188
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 74
  A := (-19767230445140685301907979/20000000000000000000000000)
  B := (9330556703534763351992609/50000000000000000000000000)
  C := (31927308801547604755199927/50000000000000000000000000)
  dδ := (17415542968060501727300959/100000000000000000000000000)
  dM := (38280799854261728099036333/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(88237934239579782769169469/10000000000000000000000000), (4664592979176977394217829/200000000000000000000000)]
  retention := ![(3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643/1188)
  hi := (859/1584)
  vmin := (622775/2509056)
  damping := (622775/2509056)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell188
