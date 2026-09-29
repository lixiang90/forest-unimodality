import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 38
  A := (16953004767431090849072461/10000000000000000000000000)
  B := (-37149086044403062389918091/50000000000000000000000000000)
  C := (-17541594883759714261148299/100000000000000000000000000000)
  dδ := (11537418820146699838247173/100000000000000000000000000)
  dM := (41039697332095485858907691/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11820809546496343855892519/2000000000000000000000000), (33669706931240874325794721/1000000000000000000000000)]
  retention := ![(4/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (131/264)
  hi := (197/396)
  vmin := (17423/69696)
  damping := (17423/69696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell079
