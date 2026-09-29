import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell406
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (63)
  A := (-13851764345185878313060357 / 20000000000000000000000000)
  B := (54675528617500565586873051 / 1000000000000000000000000000)
  C := (832558976399955588676427 / 6250000000000000000000000)
  dδ := (31116131033603597333403457 / 1000000000000000000000000000)
  dM := (477663589161906568421323 / 1000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(20378533359009223246971487 / 10000000000000000000000000), (24348486122825431010596731 / 1000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21 / 37)
  hi := (53 / 93)
  vmin := (2120 / 8649)
  damping := (2120 / 8649)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell406
