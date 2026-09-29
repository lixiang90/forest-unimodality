import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell556
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (20)
  A := (12363725023281750160286663 / 100000000000000000000000000)
  B := (1788961267084170775332197 / 100000000000000000000000000)
  C := (29703310315616279768669017 / 1000000000000000000000000000)
  dδ := (8884838677954195323982489 / 500000000000000000000000000)
  dM := (3639749722909171256992819 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(49673089220111767971843619 / 10000000000000000000000000), (3038243501613051122944853 / 2000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell556
