import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell327
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (32)
  A := (78396218098510449543425693 / 1000000000000000000000000000)
  B := (6154930833271703670417363 / 500000000000000000000000000)
  C := (24490408028018703645578569 / 1000000000000000000000000000)
  dδ := (10836763359937174808211857 / 1000000000000000000000000000)
  dM := (3956950064152286035109099 / 62500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(7685665276938405954254563 / 5000000000000000000000000), (96805491659260489711869013 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 63)
  hi := (83 / 126)
  vmin := (3569 / 15876)
  damping := (35690000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell327
