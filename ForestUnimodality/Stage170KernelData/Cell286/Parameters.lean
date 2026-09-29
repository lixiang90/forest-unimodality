import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell286
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (50)
  A := (-78092608006666609501422727 / 1000000000000000000000000000)
  B := (21208300485657367862035727 / 1000000000000000000000000000)
  C := (5870054213332952242065943 / 100000000000000000000000000)
  dδ := (16290893622509121374530849 / 1000000000000000000000000000)
  dM := (6549037066177981834379923 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(40880026347532796293648971 / 10000000000000000000000000), (641468043970479584459099 / 40000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell286
