import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell392
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (114)
  A := (-18422138478343671918935343 / 10000000000000000000000000)
  B := (91992223661234079346016301 / 1000000000000000000000000000)
  C := (466356114873594759014791 / 156250000000000000000000000)
  dδ := (26310268820990662108627589 / 500000000000000000000000000)
  dM := (16618305974693465577873841 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(19113944228377569345411757 / 1000000000000000000000000), (92994216065281278815746191 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell392
