import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell503
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (102)
  A := (-19330876757025980305826351 / 10000000000000000000000000)
  B := (323752976593992417356227 / 3125000000000000000000000)
  C := (27619340909170158465668621 / 10000000000000000000000000000)
  dδ := (1455920547109870386015551 / 25000000000000000000000000)
  dM := (10114807444835003866212553 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(7782053342258988593016511 / 1000000000000000000000000), (24356819462534122777697121 / 500000000000000000000000), (54394693961470865772867 / 1250000000000000000000)]
  retention := ![(7 / 10), (1 / 2), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22597 / 43472)
  hi := (11311 / 21736)
  vmin := (117917175 / 472453696)
  damping := (117917175 / 472453696)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell503
