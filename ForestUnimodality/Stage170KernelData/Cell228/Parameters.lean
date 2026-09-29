import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell228
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (109)
  A := (-441450671698852507152111 / 625000000000000000000000)
  B := (4522219133092480677915681 / 125000000000000000000000000)
  C := (1343736128686385256081337 / 10000000000000000000000000)
  dδ := (11565237847081119570979979 / 500000000000000000000000000)
  dM := (10269155467615573784027211 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2355319958336179197999627 / 200000000000000000000000), (7325024353640395702313981 / 200000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell228
