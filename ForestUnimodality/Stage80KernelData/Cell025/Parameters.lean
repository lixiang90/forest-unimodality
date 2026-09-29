import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 54
  A := (-13726920720028394390155313/25000000000000000000000000)
  B := (11447482253914366412406167/100000000000000000000000000)
  C := (-36224028069972435961432211/100000000000000000000000000)
  dδ := (10121687989314331890255971/100000000000000000000000000)
  dM := (20561375303966766478480643/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(42815190588108809066625327/10000000000000000000000000), (9352978475897618437784331/500000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67/153)
  hi := (4/9)
  vmin := (5762/23409)
  damping := (5762/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell025
