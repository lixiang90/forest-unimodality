import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell515
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-21440639689332442918612287 / 10000000000000000000000000)
  B := (11210237883387171031746021 / 100000000000000000000000000)
  C := (4196191923277710518480621 / 1000000000000000000000000000)
  dδ := (29223223397314198462870749 / 500000000000000000000000000)
  dM := (1371834843220359040870393 / 1250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(9127089550757503388922487 / 2000000000000000000000000), (94238151000816657187897363 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557 / 44732)
  hi := (11791 / 22366)
  vmin := (124689825 / 500237956)
  damping := (124689825 / 500237956)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell515
