import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (71)
  A := (88770871407609818213302333 / 1000000000000000000000000000)
  B := (354427460007301084812803 / 25000000000000000000000000)
  C := (-59708173083967745753408707 / 1000000000000000000000000000)
  dδ := (883833571358333034383159 / 62500000000000000000000000)
  dM := (825624847603618262123059 / 12500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(69927370581836560958777227 / 10000000000000000000000000), (4544308141645917231699059 / 200000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell087
