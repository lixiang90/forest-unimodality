import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell307
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (46)
  A := (11414477908708369762180723 / 500000000000000000000000000)
  B := (13878732802752067471141473 / 1000000000000000000000000000)
  C := (1656763166408139337226757 / 50000000000000000000000000)
  dδ := (10923466152424055747305331 / 1000000000000000000000000000)
  dM := (13076984452157458765735043 / 200000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(9194712042112197281085173 / 2000000000000000000000000), (12989079707672772201476619 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129 / 209)
  hi := (33 / 53)
  vmin := (660 / 2809)
  damping := (660 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell307
