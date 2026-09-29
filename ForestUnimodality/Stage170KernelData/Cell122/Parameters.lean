import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (177)
  A := (-5899803865805381636278071 / 5000000000000000000000000)
  B := (4896865186775550132791679 / 125000000000000000000000000)
  C := (-18110125517148087381791299 / 100000000000000000000000000)
  dδ := (24605106737598719801596303 / 1000000000000000000000000000)
  dM := (18435831718393116442078483 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(20601964821423354834450947 / 1000000000000000000000000), (12172688374694416779675521 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613 / 3478)
  hi := (22 / 47)
  vmin := (3008245 / 12096484)
  damping := (3008245 / 12096484)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell122
