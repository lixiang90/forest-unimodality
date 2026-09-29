import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell487
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (104)
  A := (-19176110542170447426002511 / 10000000000000000000000000)
  B := (1266980517392565785961267 / 12500000000000000000000000)
  C := (76215510577290381932086261 / 100000000000000000000000000000)
  dδ := (3490532971044353616196787 / 62500000000000000000000000)
  dM := (19588726806437539891547761 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(94826368300519732201792067 / 10000000000000000000000000), (92544675743300047088268911 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10429 / 20604)
  hi := (5227 / 10302)
  vmin := (26527025 / 106131204)
  damping := (26527025 / 106131204)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell487
