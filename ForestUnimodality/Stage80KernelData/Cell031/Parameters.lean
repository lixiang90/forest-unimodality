import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 106
  A := (36836233069682850938875163/100000000000000000000000000)
  B := (11099981563511347737449597/100000000000000000000000000)
  C := (-41942394002200850122719089/50000000000000000000000000)
  dδ := (4070939888600406675323029/20000000000000000000000000)
  dM := (6318262153831981928556183/2500000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2700455214573912687825441/250000000000000000000000), (38437930394155600311023591/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1677/3572)
  hi := (841/1786)
  vmin := (3177915/12759184)
  damping := (3177915/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell031
