import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (157)
  A := (-3459823567994154527838191 / 2500000000000000000000000)
  B := (59851870641343014878277273 / 1000000000000000000000000000)
  C := (-6078725968856999069267477 / 5000000000000000000000000000)
  dδ := (4175050931522127084516427 / 100000000000000000000000000)
  dM := (42978894584933755853781157 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(92050971617323593676474047 / 10000000000000000000000000), (1470339174626189293615397 / 312500000000000000000000), (14166536328814470380166313 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47 / 97)
  hi := (24 / 49)
  vmin := (2350 / 9409)
  damping := (2350 / 9409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell139
