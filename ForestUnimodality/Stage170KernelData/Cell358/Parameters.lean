import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell358
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (13049609034020460574865297 / 100000000000000000000000000)
  B := (13828610158987132347507831 / 1000000000000000000000000000)
  C := (-25973773823283662076644163 / 1000000000000000000000000000)
  dδ := (6811035749959870252978611 / 500000000000000000000000000)
  dM := (38420099884423379241193963 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(86899376785620596752579559 / 1000000000000000000000000000), (91151219793711693029081289 / 10000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (20 / 63)
  hi := (41 / 126)
  vmin := (860 / 3969)
  damping := (34400000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell358
