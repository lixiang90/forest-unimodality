import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell285
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (46)
  A := (-48510387069183697468233163 / 500000000000000000000000000)
  B := (12748234571910087645219001 / 500000000000000000000000000)
  C := (68911621201362488475794521 / 1000000000000000000000000000)
  dδ := (4918865255855947235530401 / 250000000000000000000000000)
  dM := (18440814136805476811629967 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(530911744493350212792393 / 200000000000000000000000), (7907699488362826656384641 / 500000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 180)
  hi := (3 / 5)
  vmin := (6 / 25)
  damping := (6 / 25)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell285
