import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (17124336445184624611925983 / 100000000000000000000000000)
  B := (46997618430443177314770331 / 5000000000000000000000000000)
  C := (-915108357876866468187671 / 62500000000000000000000000)
  dδ := (10464669138392800051828857 / 1000000000000000000000000000)
  dM := (17802108553670369182203581 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6898530571476645611994627 / 125000000000000000000000)]
  retention := ![(1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 140)
  hi := (19 / 70)
  vmin := (3811 / 19600)
  damping := (381100000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell009
