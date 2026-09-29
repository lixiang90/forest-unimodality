import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell430
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (21)
  A := (1423038004892194885542267 / 10000000000000000000000000)
  B := (2817035057000408584948481 / 200000000000000000000000000)
  C := (-4125698180746553006548183 / 200000000000000000000000000)
  dδ := (469247419016918224012741 / 31250000000000000000000000)
  dM := (77377870563056255662041927 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(37393698763109441962626533 / 10000000000000000000000000), (161507774677031243348857 / 78125000000000000000000)]
  retention := ![(1 / 2), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 140)
  hi := (19 / 70)
  vmin := (3811 / 19600)
  damping := (381100000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell430
