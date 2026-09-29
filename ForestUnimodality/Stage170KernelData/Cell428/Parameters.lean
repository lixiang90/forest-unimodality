import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell428
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (20)
  A := (7410665626367954839537333 / 50000000000000000000000000)
  B := (6752432741884258939057961 / 500000000000000000000000000)
  C := (-9576247549093626007521429 / 500000000000000000000000000)
  dδ := (14978637055529223087724233 / 1000000000000000000000000000)
  dM := (8890104768574734039193741 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(51757695391573017573705329 / 10000000000000000000000000), (2536868252225046686809673 / 31250000000000000000000000)]
  retention := ![(1 / 2), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell428
