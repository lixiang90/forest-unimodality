import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell362
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (33)
  A := (4018112615062208431648827 / 25000000000000000000000000)
  B := (15724536463184741325038729 / 1000000000000000000000000000)
  C := (-18948994994592169294200801 / 500000000000000000000000000)
  dδ := (15966183781659575718903099 / 1000000000000000000000000000)
  dM := (19471603330820222215943871 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(78527163951353107229635953 / 100000000000000000000000000), (1590871619928238223096173 / 1000000000000000000000000), (47535988298125841922114887 / 5000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89 / 255)
  hi := (91 / 255)
  vmin := (14774 / 65025)
  damping := (14774 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell362
