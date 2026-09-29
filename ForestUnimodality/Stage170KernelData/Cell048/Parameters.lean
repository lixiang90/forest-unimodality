import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (37)
  A := (2023273026060570900597213 / 10000000000000000000000000)
  B := (10016122670923818804844529 / 1000000000000000000000000000)
  C := (-4888594076881899730402381 / 200000000000000000000000000)
  dδ := (5565396274253620913230467 / 500000000000000000000000000)
  dM := (42977151378512574747981639 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(27143570583282525809920571 / 5000000000000000000000000), (73615788347813557734866663 / 10000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 3)
  hi := (29 / 85)
  vmin := (2 / 9)
  damping := (80000000000000000000000000000000000000000 / 888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell048
