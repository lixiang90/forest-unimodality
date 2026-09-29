import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (69)
  A := (47363222957560912060870351 / 1000000000000000000000000000)
  B := (10827798477028367785113261 / 1000000000000000000000000000)
  C := (-9803248453575942947257893 / 250000000000000000000000000)
  dδ := (95466401232848496771765667 / 10000000000000000000000000000)
  dM := (4077497370929685318631519 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(83192247896267161877403851 / 10000000000000000000000000), (2009115350527560650562009 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103 / 255)
  hi := (7 / 17)
  vmin := (15656 / 65025)
  damping := (15656 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell083
