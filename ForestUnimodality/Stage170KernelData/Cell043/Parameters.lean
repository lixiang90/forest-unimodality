import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (36)
  A := (1449284465133531363356667 / 10000000000000000000000000)
  B := (8827599206567572284742873 / 1000000000000000000000000000)
  C := (-8924606796626013277551337 / 500000000000000000000000000)
  dδ := (21823598667837888764875487 / 2500000000000000000000000000)
  dM := (1048134968108650370027953 / 31250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(17076689577232682104579453 / 5000000000000000000000000), (87030218780064281247632607 / 10000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell043
