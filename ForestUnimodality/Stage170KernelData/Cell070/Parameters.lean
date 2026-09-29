import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (53)
  A := (2623485147055862457099451 / 12500000000000000000000000)
  B := (44443153754814617925616993 / 5000000000000000000000000000)
  C := (-15873411859640213644739859 / 500000000000000000000000000)
  dδ := (98236228264937976162318733 / 10000000000000000000000000000)
  dM := (8713432347653307197092587 / 250000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(54539334581965857040586343 / 10000000000000000000000000), (15290855495256177931651109 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 255)
  hi := (33 / 85)
  vmin := (15326 / 65025)
  damping := (15326 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell070
