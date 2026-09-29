import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell341
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (23)
  A := (20322049046781980878861873 / 500000000000000000000000000)
  B := (8815537164103558892547241 / 500000000000000000000000000)
  C := (5026422363518406183358067 / 200000000000000000000000000)
  dδ := (7101416829722009133041283 / 500000000000000000000000000)
  dM := (12114015279330019730918977 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(310318309215885046459249 / 125000000000000000000000), (12226418876710796190820929 / 2500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 78)
  hi := (107 / 156)
  vmin := (5243 / 24336)
  damping := (13107500000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell341
