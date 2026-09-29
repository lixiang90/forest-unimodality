import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell199
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (168)
  A := (-638838914963828115475053 / 400000000000000000000000)
  B := (62639251713847127200907039 / 1000000000000000000000000000)
  C := (29263962145599830069753189 / 10000000000000000000000000000)
  dδ := (317774158790009142450117 / 8000000000000000000000000)
  dM := (8550191687815184319806927 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(7163133172305641060972903 / 500000000000000000000000), (15203985099434493122316781 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28 / 53)
  hi := (113 / 213)
  vmin := (11300 / 45369)
  damping := (11300 / 45369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell199
