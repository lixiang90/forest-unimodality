import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell537
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (59)
  A := (-1390250573563992599872563 / 2000000000000000000000000)
  B := (60030279175864925678141049 / 1000000000000000000000000000)
  C := (7083814469487025033966887 / 50000000000000000000000000)
  dδ := (17383813545410121276235671 / 500000000000000000000000000)
  dM := (1775160710124834564861869 / 3125000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2500573323488988197738081 / 125000000000000000000000), (45001982948470455880851659 / 10000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell537
