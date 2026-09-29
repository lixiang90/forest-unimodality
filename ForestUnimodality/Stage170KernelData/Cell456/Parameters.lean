import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell456
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (112)
  A := (-18043889211195966348810771 / 10000000000000000000000000)
  B := (334623881567937438152871 / 3125000000000000000000000)
  C := (-32156250071050501704306157 / 100000000000000000000000000)
  dδ := (59792730718542623502553823 / 1000000000000000000000000000)
  dM := (10237397288312031443796579 / 10000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(18667360631357649225492423 / 1000000000000000000000000), (31089400903270252740639989 / 1000000000000000000000000)]
  retention := ![(3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17 / 37)
  hi := (1613 / 3478)
  vmin := (340 / 1369)
  damping := (340 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell456
