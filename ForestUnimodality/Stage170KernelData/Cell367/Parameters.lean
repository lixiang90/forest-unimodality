import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell367
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (44)
  A := (4763969858692953309287077 / 200000000000000000000000000)
  B := (154385653663811683866669 / 8000000000000000000000000)
  C := (-6886997269676519567438433 / 125000000000000000000000000)
  dδ := (16836563161415355610595057 / 1000000000000000000000000000)
  dM := (12405465035448577518564783 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7834900882648959452581039 / 2000000000000000000000000), (13461897847042319398269683 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 85)
  hi := (101 / 255)
  vmin := (1716 / 7225)
  damping := (1716 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell367
