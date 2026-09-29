import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell399
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (94)
  A := (-1448796482184867274725093 / 1000000000000000000000000)
  B := (2625352480478021586357551 / 31250000000000000000000000)
  C := (11062780257084302293346667 / 50000000000000000000000000)
  dδ := (10640773957062305346554787 / 250000000000000000000000000)
  dM := (37035326813612178204274117 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(8426357040125845854205977 / 1250000000000000000000000), (17136790956008631781060103 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6 / 11)
  hi := (97 / 177)
  vmin := (7760 / 31329)
  damping := (7760 / 31329)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell399
