import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 44
  A := (-1288538571969008091055997/1250000000000000000000000)
  B := (17795608074812169219214297/100000000000000000000000000)
  C := (9657778145247772338954917/25000000000000000000000000)
  dδ := (311540067985952989770837/2500000000000000000000000)
  dM := (9331165280254604885157299/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8844047990441968876140777/10000000000000000000000000), (16704281972984990289887719/1000000000000000000000000)]
  retention := ![(7/20), (3/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell202
