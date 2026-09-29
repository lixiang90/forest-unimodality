import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell212
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (173)
  A := (-6541836350568450369991069 / 5000000000000000000000000)
  B := (41458006121023856238583249 / 1000000000000000000000000000)
  C := (4313822751137291744427671 / 25000000000000000000000000)
  dδ := (11712709372924309456087677 / 500000000000000000000000000)
  dM := (19592595406474406951984057 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15640940549375637047546661 / 500000000000000000000000), (48054904797670815241872333 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell212
