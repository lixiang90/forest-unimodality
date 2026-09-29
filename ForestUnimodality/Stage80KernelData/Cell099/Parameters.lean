import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-26193334186028620734987271/100000000000000000000000000)
  B := (260491286286657214299467/2500000000000000000000000)
  C := (26038925362867663092225623/5000000000000000000000000000)
  dδ := (12597550936036858160171903/100000000000000000000000000)
  dM := (1476783525857881666006749/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55438479781900538156946823/10000000000000000000000000), (11817398401978536526257813/1000000000000000000000000), (21256062553682898652596123/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/103)
  hi := (21967/42642)
  vmin := (454167725/1818340164)
  damping := (454167725/1818340164)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell099
