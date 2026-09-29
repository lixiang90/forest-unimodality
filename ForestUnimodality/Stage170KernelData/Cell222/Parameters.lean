import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell222
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (108)
  A := (-42328107959234053724983937 / 50000000000000000000000000)
  B := (46459387448512724783089567 / 1000000000000000000000000000)
  C := (4243720982897358079410921 / 25000000000000000000000000)
  dδ := (29868451794548528388517639 / 1000000000000000000000000000)
  dM := (7641942712293866288904981 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(38624860228667032835403461 / 5000000000000000000000000), (40319767594880566718984483 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6 / 11)
  hi := (97 / 177)
  vmin := (7760 / 31329)
  damping := (7760 / 31329)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell222
