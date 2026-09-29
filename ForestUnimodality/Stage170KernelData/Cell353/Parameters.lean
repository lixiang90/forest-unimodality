import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell353
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (24)
  A := (447737133311818347902733 / 3125000000000000000000000)
  B := (531450415837403794538929 / 40000000000000000000000000)
  C := (-2049704080211522602694707 / 100000000000000000000000000)
  dδ := (2746026947276311233614443 / 200000000000000000000000000)
  dM := (67927466372024524290419711 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(69451572974842541441375943 / 10000000000000000000000000), (5261066694983490901749157 / 250000000000000000000000000)]
  retention := ![(1 / 2), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39 / 140)
  hi := (2 / 7)
  vmin := (3939 / 19600)
  damping := (393900000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell353
