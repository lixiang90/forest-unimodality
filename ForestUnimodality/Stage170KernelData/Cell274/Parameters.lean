import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell274
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (-19978181781252983938657053 / 100000000000000000000000000)
  B := (25731160092175565240468771 / 1000000000000000000000000000)
  C := (19554485032401751343211771 / 250000000000000000000000000)
  dδ := (2356583283637460075193859 / 125000000000000000000000000)
  dM := (648923682934252911945483 / 4000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(4799902878229015179556427 / 1000000000000000000000000), (2059031143514840067609839 / 100000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653 / 1128)
  hi := (7 / 12)
  vmin := (35 / 144)
  damping := (35 / 144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell274
