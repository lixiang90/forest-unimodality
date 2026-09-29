import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell470
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (94)
  A := (-21323569774375172214320173 / 10000000000000000000000000)
  B := (11583802305260816611909291 / 100000000000000000000000000)
  C := (-870172098825944609346017 / 400000000000000000000000000)
  dδ := (29143256035586651009339221 / 500000000000000000000000000)
  dM := (11869732933414223544077437 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(98134900607689132812083699 / 10000000000000000000000000), (81998051879969466426700819 / 1000000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47 / 97)
  hi := (9237 / 19012)
  vmin := (2350 / 9409)
  damping := (2350 / 9409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell470
