import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell477
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (99)
  A := (-10416567233903126449234833 / 5000000000000000000000000)
  B := (10959011882562563755527663 / 100000000000000000000000000)
  C := (-526011670993955320041989 / 625000000000000000000000000)
  dδ := (7102363793173665194868871 / 125000000000000000000000000)
  dM := (1348979603546245249756641 / 1250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(37875420339482617215765003 / 10000000000000000000000000), (5817073576724979488972167 / 62500000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3193 / 6468)
  hi := (49 / 99)
  vmin := (10457075 / 41835024)
  damping := (10457075 / 41835024)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell477
