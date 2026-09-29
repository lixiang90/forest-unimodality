import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell467
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (95)
  A := (-19810156805615545716392489 / 10000000000000000000000000)
  B := (11035808562265740639940503 / 100000000000000000000000000)
  C := (-29355208407200522255364739 / 10000000000000000000000000000)
  dδ := (60818347513944784332728943 / 1000000000000000000000000000)
  dM := (2256523981142726821558231 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1698108987701194561026341 / 125000000000000000000000), (15875247918231133326116833 / 200000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2983 / 6208)
  hi := (4487 / 9312)
  vmin := (9620175 / 38539264)
  damping := (9620175 / 38539264)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell467
