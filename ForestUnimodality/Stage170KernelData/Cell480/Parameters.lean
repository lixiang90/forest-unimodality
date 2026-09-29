import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell480
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-20103238221605023616689323 / 10000000000000000000000000)
  B := (5305567440132284706688637 / 50000000000000000000000000)
  C := (-36131785329461667525435039 / 5000000000000000000000000000000)
  dδ := (57928294444552448638763309 / 1000000000000000000000000000)
  dM := (645186297192730994973231 / 625000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(17158283916202314856036537 / 10000000000000000000000000), (98215936718131757743321941 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (197 / 396)
  hi := (395 / 792)
  vmin := (39203 / 156816)
  damping := (39203 / 156816)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell480
