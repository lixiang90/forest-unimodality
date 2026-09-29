import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell237
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (92)
  A := (-56609515281307425492940411 / 100000000000000000000000000)
  B := (38081131307173464450865907 / 1000000000000000000000000000)
  C := (13907916451453294914841763 / 100000000000000000000000000)
  dδ := (26432500270982157986043859 / 1000000000000000000000000000)
  dM := (6197763961358333610878607 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(36613150413681814221433797 / 5000000000000000000000000), (16531545767709623362407001 / 500000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99 / 179)
  hi := (5 / 9)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell237
