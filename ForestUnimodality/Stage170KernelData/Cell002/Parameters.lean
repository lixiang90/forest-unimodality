import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (26)
  A := (1741278415029912196665407 / 10000000000000000000000000)
  B := (37992565525226582555384791 / 5000000000000000000000000000)
  C := (-11513103318110928449669039 / 1000000000000000000000000000)
  dδ := (4418336439924530970047023 / 500000000000000000000000000)
  dM := (24066371143386331430454733 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(36744238907860705012353719 / 1000000000000000000000000), (10667368870916700984707859 / 25000000000000000000000)]
  retention := ![(1 / 2), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell002
