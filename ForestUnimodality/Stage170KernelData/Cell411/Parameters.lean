import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell411
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (50)
  A := (-42264904795529300129075523 / 100000000000000000000000000)
  B := (43021756691954876616890147 / 1000000000000000000000000000)
  C := (98860346294932816002543063 / 1000000000000000000000000000)
  dδ := (26499627870800623874458779 / 1000000000000000000000000000)
  dM := (7392225479701550281547151 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2335780215271180682012897 / 1250000000000000000000000), (4604177534748841615908077 / 250000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell411
