import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell190
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (209)
  A := (-15973377704809729637958071 / 10000000000000000000000000)
  B := (841680462665617221823533 / 15625000000000000000000000)
  C := (909672025729016744954869 / 400000000000000000000000000)
  dδ := (1082004435891742531034021 / 31250000000000000000000000)
  dM := (31590625390670449331581571 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(13340190777764107110670011 / 500000000000000000000000), (4517248517802665475073809 / 25000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (111 / 211)
  vmin := (11100 / 44521)
  damping := (11100 / 44521)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell190
