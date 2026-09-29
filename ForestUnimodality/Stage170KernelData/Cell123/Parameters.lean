import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (133)
  A := (-692122988110569333116473 / 400000000000000000000000)
  B := (77864612868763907749247721 / 1000000000000000000000000000)
  C := (-3969379672786260498072719 / 1250000000000000000000000000)
  dδ := (23387213061481150477849411 / 500000000000000000000000000)
  dM := (15628211816005914891122841 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(4666901363453138884551663 / 200000000000000000000000), (1078915967900731516238011 / 10000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 47)
  hi := (9 / 19)
  vmin := (550 / 2209)
  damping := (550 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell123
