import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell472
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (95)
  A := (-40257712694868973213147 / 20000000000000000000000)
  B := (11188378189468964341024559 / 100000000000000000000000000)
  C := (-3775114558509557491187969 / 2500000000000000000000000000)
  dδ := (60410598431665032959081429 / 1000000000000000000000000000)
  dM := (143402988927109086882139 / 125000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(4407394360359367380119977 / 1250000000000000000000000), (89402308324360802771479939 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631 / 9506)
  hi := (9287 / 19012)
  vmin := (22576125 / 90364036)
  damping := (22576125 / 90364036)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell472
