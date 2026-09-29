import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell301
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (45)
  A := (-21980775534775698893952267 / 500000000000000000000000000)
  B := (8871948384912547308500663 / 500000000000000000000000000)
  C := (1028313522755569878186499 / 25000000000000000000000000)
  dδ := (1310723173741680513959551 / 100000000000000000000000000)
  dM := (48633708613623386309617741 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(13346551541902453852372901 / 10000000000000000000000000), (16042881677432369258440303 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63 / 103)
  hi := (129 / 209)
  vmin := (10320 / 43681)
  damping := (10320 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell301
