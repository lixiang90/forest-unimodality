import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-435861184734842200394489/625000000000000000000000)
  B := (95179376641528104507905539/1000000000000000000000000000)
  C := (23272092323275350364553127/5000000000000000000000000000)
  dδ := (90527936326774333108957649/1000000000000000000000000000)
  dM := (1968126228978740537532699/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7196565970495257147376833/1000000000000000000000000), (1680807704642674593742413/40000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583/8778)
  hi := (2294/4389)
  vmin := (4805930/19263321)
  damping := (4805930/19263321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell110
