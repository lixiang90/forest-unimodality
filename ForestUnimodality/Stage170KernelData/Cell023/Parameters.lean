import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (16945358301152131264899481 / 100000000000000000000000000)
  B := (41265613813222783851086817 / 5000000000000000000000000000)
  C := (-14093910865951133140616669 / 1000000000000000000000000000)
  dδ := (22288043064516492412774351 / 2500000000000000000000000000)
  dM := (1817917202836851323742161 / 62500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(26719911203059659499103873 / 1000000000000000000000000), (24847201112979075077191737 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell023
