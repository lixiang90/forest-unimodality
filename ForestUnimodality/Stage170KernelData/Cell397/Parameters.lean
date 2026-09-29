import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell397
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (113)
  A := (-17484073380658957008648713 / 10000000000000000000000000)
  B := (96262672022605674793105379 / 1000000000000000000000000000)
  C := (14159283139894632275179731 / 50000000000000000000000000)
  dδ := (50856972436870366560679457 / 1000000000000000000000000000)
  dM := (17139464497279938235557717 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1364172720094022794867783 / 125000000000000000000000), (39318993080761963199165621 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 54)
  hi := (643 / 1188)
  vmin := (350435 / 1411344)
  damping := (350435 / 1411344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell397
