import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell431
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (22)
  A := (6700802747337234411162399 / 50000000000000000000000000)
  B := (745954802021265694217389 / 50000000000000000000000000)
  C := (-22295456847451607107490901 / 1000000000000000000000000000)
  dδ := (3100122199335492850780227 / 200000000000000000000000000)
  dM := (83575303427721505116106127 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(4557604308447856800157183 / 1250000000000000000000000), (12893589844578803305097381 / 5000000000000000000000000)]
  retention := ![(9 / 20), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell431
