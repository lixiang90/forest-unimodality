import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell270
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (64)
  A := (-6262447453676211778006433 / 25000000000000000000000000)
  B := (27159814915991089406821501 / 1000000000000000000000000000)
  C := (20967044345598883497983067 / 250000000000000000000000000)
  dδ := (4853643296286598921018829 / 250000000000000000000000000)
  dM := (3452850797496775903626387 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(49829901666467462106879793 / 10000000000000000000000000), (2189728173783014497644217 / 100000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 47)
  hi := (653 / 1128)
  vmin := (310175 / 1272384)
  damping := (310175 / 1272384)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell270
