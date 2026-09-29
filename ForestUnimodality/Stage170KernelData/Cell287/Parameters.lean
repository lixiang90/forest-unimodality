import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell287
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (53)
  A := (-25109444045422358851027411 / 1000000000000000000000000000)
  B := (8579889027443818316776003 / 500000000000000000000000000)
  C := (12815772553813440867709339 / 250000000000000000000000000)
  dδ := (13959892781634312616811933 / 1000000000000000000000000000)
  dM := (46006859604576823003906777 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15276705443845315812723129 / 2000000000000000000000000), (688288464773973807098173 / 50000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 180)
  hi := (3 / 5)
  vmin := (6 / 25)
  damping := (6 / 25)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell287
