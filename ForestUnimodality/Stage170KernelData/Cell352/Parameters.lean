import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell352
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (23)
  A := (14072368587583773292593037 / 100000000000000000000000000)
  B := (6578813735151564819070291 / 500000000000000000000000000)
  C := (-10016597703196090246580141 / 500000000000000000000000000)
  dδ := (1383485556857837195376959 / 100000000000000000000000000)
  dM := (665211711479941013823447 / 10000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(11970688426057112252465231 / 5000000000000000000000000), (643729813564636599299007 / 156250000000000000000000)]
  retention := ![(1 / 2), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 70)
  hi := (39 / 140)
  vmin := (969 / 4900)
  damping := (387600000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell352
