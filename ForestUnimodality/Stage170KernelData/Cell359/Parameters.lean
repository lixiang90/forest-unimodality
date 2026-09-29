import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell359
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (29)
  A := (7177383588537412040686547 / 50000000000000000000000000)
  B := (3353223072615995042217163 / 250000000000000000000000000)
  C := (-5416902291137876135351803 / 200000000000000000000000000)
  dδ := (1685283641327766810877331 / 125000000000000000000000000)
  dM := (75128850204676507571616151 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(34228476374163979700782079 / 50000000000000000000000000), (39843609461139040117672039 / 100000000000000000000000000), (43433259678782167867439057 / 5000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell359
