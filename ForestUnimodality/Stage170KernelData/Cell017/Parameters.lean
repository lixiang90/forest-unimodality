import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (3913324137128736363244741 / 25000000000000000000000000)
  B := (19249521805828090359469229 / 2000000000000000000000000000)
  C := (-3848545482510168196099709 / 250000000000000000000000000)
  dδ := (2549441173064084277533059 / 250000000000000000000000000)
  dM := (37755805474815115477856681 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(39037880126349520537587523 / 1000000000000000000000000)]
  retention := ![(1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell017
