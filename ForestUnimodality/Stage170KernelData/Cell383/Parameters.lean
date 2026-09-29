import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell383
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (109)
  A := (-544285955449955821947583 / 250000000000000000000000)
  B := (2159434391812469211657799 / 20000000000000000000000000)
  C := (-12928990314842181419408007 / 10000000000000000000000000000)
  dδ := (27695878012270632589908459 / 500000000000000000000000000)
  dM := (2522233048150714453984611 / 2500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(10342316713128212324335209 / 10000000000000000000000000), (56932314148037894696585681 / 10000000000000000000000000), (2501032605877285419637701 / 25000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24 / 49)
  hi := (49 / 99)
  vmin := (600 / 2401)
  damping := (600 / 2401)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell383
