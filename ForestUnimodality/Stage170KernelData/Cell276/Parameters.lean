import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell276
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (70)
  A := (-2829172070611620592828217 / 20000000000000000000000000)
  B := (8848897283324826806838459 / 500000000000000000000000000)
  C := (5708900711907431008151903 / 100000000000000000000000000)
  dδ := (13032891327324840416435059 / 1000000000000000000000000000)
  dM := (83065821201701398610386939 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(856581093356207912137279 / 62500000000000000000000), (15560082358933627233454899 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653 / 1128)
  hi := (7 / 12)
  vmin := (35 / 144)
  damping := (35 / 144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell276
