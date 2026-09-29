import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 15
  A := (55948272532779947830761103/100000000000000000000000000)
  B := (152243227543060327677793/10000000000000000000000000)
  C := (18689684447686344404004899/250000000000000000000000000)
  dδ := (23881211922463525115789551/500000000000000000000000000)
  dM := (27339873240793128705145021/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8503411747364709727392551/2500000000000000000000000), (18432991724382237208601509/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/78)
  hi := (107/156)
  vmin := (5243/24336)
  damping := (13107500000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell234
