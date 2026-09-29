import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell400
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (89)
  A := (-6521990492325697391606809 / 5000000000000000000000000)
  B := (78571758868189345292876169 / 1000000000000000000000000000)
  C := (2074967236941085702017773 / 10000000000000000000000000)
  dδ := (40981300862359272552115641 / 1000000000000000000000000000)
  dM := (69124671786507268546329019 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(71129754066782870935981009 / 10000000000000000000000000), (31560147170865089805147363 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 177)
  hi := (49 / 89)
  vmin := (1960 / 7921)
  damping := (1960 / 7921)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell400
