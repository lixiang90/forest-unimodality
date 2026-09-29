import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell344
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (8117150676346976263531019 / 125000000000000000000000000)
  B := (10585386961381226811340639 / 1000000000000000000000000000)
  C := (1950167724192258290882851 / 125000000000000000000000000)
  dδ := (86616327534675893740079289 / 10000000000000000000000000000)
  dM := (11933706947072056757798257 / 250000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(11074701529064969740545621 / 10000000000000000000000000), (39537865261582809672802341 / 5000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 78)
  hi := (107 / 156)
  vmin := (5243 / 24336)
  damping := (13107500000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell344
