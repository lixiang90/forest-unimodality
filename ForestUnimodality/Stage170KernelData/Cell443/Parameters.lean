import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell443
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (35)
  A := (18927427710018597140972929 / 100000000000000000000000000)
  B := (8450353583483987546243199 / 500000000000000000000000000)
  C := (-12370000750771300082608839 / 250000000000000000000000000)
  dδ := (18618921616984647482428983 / 1000000000000000000000000000)
  dM := (1165790139839492623417827 / 10000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(883138806669301956731033 / 400000000000000000000000), (5476277010937553590963489 / 500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31 / 85)
  hi := (19 / 51)
  vmin := (1674 / 7225)
  damping := (1674 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell443
