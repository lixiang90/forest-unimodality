import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (24)
  A := (2030819641882179851899437 / 12500000000000000000000000)
  B := (88681653356792421172283269 / 10000000000000000000000000000)
  C := (-6522335257021802910892827 / 500000000000000000000000000)
  dδ := (5041528553320473622634257 / 500000000000000000000000000)
  dM := (1008916197525522513608583 / 31250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1208776396318175194721789 / 25000000000000000000000)]
  retention := ![(1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 4)
  hi := (9 / 35)
  vmin := (3 / 16)
  damping := (7500000000000000000000000000000000000000 / 98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell001
