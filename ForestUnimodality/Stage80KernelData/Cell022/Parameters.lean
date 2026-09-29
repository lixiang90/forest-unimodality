import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 41
  A := (-36607243627878357560945233/50000000000000000000000000)
  B := (734506723515182275568991/6250000000000000000000000)
  C := (-25364613341895092535338563/100000000000000000000000000)
  dδ := (40090795658945931057015599/500000000000000000000000000)
  dM := (20135030029733726707197317/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(11076005081367614746312711/5000000000000000000000000), (7068568520013412737057479/500000000000000000000000)]
  retention := ![(2/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64/153)
  hi := (65/153)
  vmin := (5696/23409)
  damping := (5696/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell022
