import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (58)
  A := (10705370061117486097934659 / 125000000000000000000000000)
  B := (289021058662710782910521 / 25000000000000000000000000)
  C := (-40006537153973793785599611 / 1000000000000000000000000000)
  dδ := (5369818387464750548965231 / 500000000000000000000000000)
  dM := (3108068150399467749136909 / 62500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(250900334483166786991859 / 62500000000000000000000), (19447952415221529065547657 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101 / 255)
  hi := (103 / 255)
  vmin := (15554 / 65025)
  damping := (15554 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell077
