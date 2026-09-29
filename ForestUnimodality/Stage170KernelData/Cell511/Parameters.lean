import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell511
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-2264218279383023381114981 / 1000000000000000000000000)
  B := (11688259049136021094916771 / 100000000000000000000000000)
  C := (38017002438719216597662331 / 10000000000000000000000000000)
  dδ := (14403545844131285941225329 / 250000000000000000000000000)
  dM := (11480476704815280666882593 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1210304237995727616450381 / 500000000000000000000000), (12032671345186610523114723 / 125000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549 / 2954)
  hi := (2326 / 4431)
  vmin := (4896230 / 19633761)
  damping := (4896230 / 19633761)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell511
