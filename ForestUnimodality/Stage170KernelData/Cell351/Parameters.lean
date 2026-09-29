import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell351
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (22)
  A := (1334947563211290144735699 / 10000000000000000000000000)
  B := (12594139099082584873356971 / 1000000000000000000000000000)
  C := (-18254116024660069911300653 / 1000000000000000000000000000)
  dδ := (13221628908560840304220463 / 1000000000000000000000000000)
  dM := (3880375436724012830249763 / 62500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(475076923548248764017643 / 250000000000000000000000), (41731498886234836831476969 / 10000000000000000000000000)]
  retention := ![(1 / 2), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell351
