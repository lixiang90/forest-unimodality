import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell260
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (70)
  A := (-35509399884982821959056309 / 100000000000000000000000000)
  B := (7704205939492502451526601 / 250000000000000000000000000)
  C := (47010303502998930513800957 / 500000000000000000000000000)
  dδ := (20865242834277285266519897 / 1000000000000000000000000000)
  dM := (245903685688513455934439 / 1250000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(11385630977177905176489503 / 2500000000000000000000000), (6270826160539790805614757 / 250000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 93)
  hi := (107 / 187)
  vmin := (8560 / 34969)
  damping := (8560 / 34969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell260
