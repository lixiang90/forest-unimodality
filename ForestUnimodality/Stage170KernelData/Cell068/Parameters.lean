import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (3951452822082875049503059 / 20000000000000000000000000)
  B := (1409992914623558199829767 / 125000000000000000000000000)
  C := (-196399558999451745444631 / 5000000000000000000000000)
  dδ := (12433521070007636302734433 / 1000000000000000000000000000)
  dM := (27499912169421802406567637 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(23811359452524571977960477 / 10000000000000000000000000), (16011792086511196231413123 / 1000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell068
