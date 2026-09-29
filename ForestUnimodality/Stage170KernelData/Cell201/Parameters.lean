import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell201
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (255)
  A := (-18358501216068107597578773 / 10000000000000000000000000)
  B := (6440420579594909912535261 / 125000000000000000000000000)
  C := (22530293044446163611138623 / 10000000000000000000000000000)
  dδ := (1193631518220417686571011 / 40000000000000000000000000)
  dM := (6569266923721446755409653 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(42828700074004558473461657 / 1000000000000000000000000), (21030787204573758231163083 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28 / 53)
  hi := (113 / 213)
  vmin := (11300 / 45369)
  damping := (11300 / 45369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell201
