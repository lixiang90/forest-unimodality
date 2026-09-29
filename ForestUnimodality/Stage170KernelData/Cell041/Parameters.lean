import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (7151237834509577784736223 / 50000000000000000000000000)
  B := (11777456143972575564049521 / 1000000000000000000000000000)
  C := (-23858064289456575035597297 / 1000000000000000000000000000)
  dδ := (588490971808988856672773 / 50000000000000000000000000)
  dM := (58286104938986235972277899 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(11259320188373380666746471 / 10000000000000000000000000), (23287020468651369320411959 / 2500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 126)
  hi := (1 / 3)
  vmin := (3485 / 15876)
  damping := (34850000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell041
