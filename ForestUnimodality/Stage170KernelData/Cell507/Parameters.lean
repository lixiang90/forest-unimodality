import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell507
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-4966873443009521663071837 / 2500000000000000000000000)
  B := (10555526966818409850823457 / 100000000000000000000000000)
  C := (30875342073807157498854803 / 10000000000000000000000000000)
  dδ := (2866925009679769167925123 / 50000000000000000000000000)
  dM := (2066224462662706942706059 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(87541900592241006506810663 / 10000000000000000000000000), (45102409798792940875955537 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583 / 8778)
  hi := (2294 / 4389)
  vmin := (4805930 / 19263321)
  damping := (4805930 / 19263321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell507
