import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (149)
  A := (-16221521879107904562289377 / 10000000000000000000000000)
  B := (4310254326446208081313749 / 62500000000000000000000000)
  C := (-25938475675861766278629261 / 100000000000000000000000000)
  dδ := (20142134510447287643053471 / 500000000000000000000000000)
  dM := (46234120576780943180292271 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(29357503189873852988966973 / 1000000000000000000000000), (38465366447514547587616107 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell119
