import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell423
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (10312875017946261269941033 / 100000000000000000000000000)
  B := (18934601377051912818316737 / 1000000000000000000000000000)
  C := (36451604192573879015260019 / 1000000000000000000000000000)
  dδ := (9033289965846536331839367 / 500000000000000000000000000)
  dM := (15102155286193113831877399 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(20597741891328462671140187 / 2500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (83 / 126)
  hi := (2 / 3)
  vmin := (2 / 9)
  damping := (80000000000000000000000000000000000000000 / 888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell423
