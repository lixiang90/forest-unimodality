import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell525
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-9721932286189544863930223 / 5000000000000000000000000)
  B := (5189541337175061774811269 / 50000000000000000000000000)
  C := (22342438842323062049566307 / 5000000000000000000000000000)
  dδ := (56854762448806848984528273 / 1000000000000000000000000000)
  dM := (5086382354054972375345667 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(95684114676743234895184287 / 10000000000000000000000000), (8843482580041062135478569 / 100000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24257 / 45582)
  hi := (57 / 107)
  vmin := (2850 / 11449)
  damping := (2850 / 11449)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell525
