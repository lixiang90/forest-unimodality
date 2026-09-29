import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (43)
  A := (9727993921108047337575897 / 50000000000000000000000000)
  B := (998666978813643468892991 / 100000000000000000000000000)
  C := (-27306778705764828824031909 / 1000000000000000000000000000)
  dδ := (10437782577924711174821581 / 1000000000000000000000000000)
  dM := (20887945608933354714855171 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(77900658023827018539009259 / 100000000000000000000000000), (13823954172374015580970763 / 5000000000000000000000000), (1536922605450297130147419 / 125000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell057
