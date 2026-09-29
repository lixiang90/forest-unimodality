import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-16603660192439445075329729 / 50000000000000000000000000)
  B := (20343253099073407841324013 / 1000000000000000000000000000)
  C := (-42270039024162778251714201 / 500000000000000000000000000)
  dδ := (7436700089037092016586161 / 500000000000000000000000000)
  dM := (9089029986800231523166177 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(98434330429739080869921963 / 10000000000000000000000000), (3461397916382935591173009 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67 / 153)
  hi := (4 / 9)
  vmin := (5762 / 23409)
  damping := (5762 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell103
