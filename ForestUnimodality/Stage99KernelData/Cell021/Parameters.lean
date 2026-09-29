import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 43
  A := (-24535091067625385385042591/100000000000000000000000000)
  B := (5877009877874189713864439/100000000000000000000000000)
  C := (-16645250256619986695127977/100000000000000000000000000)
  dδ := (49882665432516792858308463/1000000000000000000000000000)
  dM := (4636950115121102734914299/6250000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6532540578872093384177333/2000000000000000000000000), (2851796347292569677733809/200000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7/17)
  hi := (64/153)
  vmin := (70/289)
  damping := (70/289)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell021
