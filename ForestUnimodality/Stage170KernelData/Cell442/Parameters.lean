import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell442
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (33)
  A := (17490257922392355883545179 / 100000000000000000000000000)
  B := (4262093608848028201963043 / 250000000000000000000000000)
  C := (-5660869203746325163673081 / 125000000000000000000000000)
  dδ := (18122043085638570025786009 / 1000000000000000000000000000)
  dM := (145855202966182606589109 / 1250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(13690660853716689615566793 / 10000000000000000000000000), (10702502281485292812135413 / 1000000000000000000000000), (3761466664920013608375271 / 50000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (91 / 255)
  hi := (31 / 85)
  vmin := (14924 / 65025)
  damping := (14924 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell442
