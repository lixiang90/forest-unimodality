import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell370
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (55)
  A := (-14333982473250137744003041 / 200000000000000000000000000)
  B := (14323068705514137993750623 / 500000000000000000000000000)
  C := (-24590127713115136204313771 / 250000000000000000000000000)
  dδ := (25677134533651335690507267 / 1000000000000000000000000000)
  dM := (4362428448699438507385473 / 20000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10802304275952433698648747 / 2000000000000000000000000), (2176210781497979862564307 / 125000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell370
