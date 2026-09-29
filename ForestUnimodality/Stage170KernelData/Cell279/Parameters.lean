import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell279
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (-1513489522484249991007843 / 12500000000000000000000000)
  B := (2444552022063417942576713 / 125000000000000000000000000)
  C := (60404410928966138782936213 / 1000000000000000000000000000)
  dδ := (14770823159503497848388243 / 1000000000000000000000000000)
  dM := (10513201482752486436503259 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(19822139244206056218899903 / 2500000000000000000000000), (4322891643274259010354399 / 250000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 12)
  hi := (53 / 90)
  vmin := (1961 / 8100)
  damping := (1961 / 8100)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell279
