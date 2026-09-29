import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell402
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (81)
  A := (-87509947028428585301895737 / 100000000000000000000000000)
  B := (3937313927819418094000703 / 62500000000000000000000000)
  C := (18779432555512937108588289 / 100000000000000000000000000)
  dδ := (19527140666162342425016263 / 500000000000000000000000000)
  dM := (54947224001585599946484439 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(12412685042029576010236269 / 1000000000000000000000000), (907459767969377253393759 / 40000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99 / 179)
  hi := (5 / 9)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell402
