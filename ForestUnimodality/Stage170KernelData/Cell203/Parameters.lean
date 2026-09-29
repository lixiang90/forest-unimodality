import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell203
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (136)
  A := (-19823189664533106724064737 / 10000000000000000000000000)
  B := (84671912222446119034025003 / 1000000000000000000000000000)
  C := (7067943045448875707958969 / 2000000000000000000000000000)
  dδ := (9205129905583063487650719 / 200000000000000000000000000)
  dM := (2090427056560692511640899 / 3125000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16076456036794386506016963 / 500000000000000000000000), (10182228728195273959045153 / 100000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113 / 213)
  hi := (57 / 107)
  vmin := (2850 / 11449)
  damping := (2850 / 11449)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell203
