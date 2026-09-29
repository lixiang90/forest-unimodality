import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (44)
  A := (20596806122999967604059179 / 100000000000000000000000000)
  B := (1251732825111244278015743 / 125000000000000000000000000)
  C := (-27840779975196117829172593 / 1000000000000000000000000000)
  dδ := (10625266601718119305330923 / 1000000000000000000000000000)
  dM := (5199071819408287100532963 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1980801923200869341101793 / 2000000000000000000000000), (1192484447373982764384337 / 625000000000000000000000), (665809738039225695871437 / 50000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell058
