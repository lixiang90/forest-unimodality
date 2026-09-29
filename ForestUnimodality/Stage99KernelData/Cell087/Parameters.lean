import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 61
  A := (-39311121642217857147239/39062500000000000000000)
  B := (96272410518530596168496061/1000000000000000000000000000)
  C := (13869725892139480195180967/5000000000000000000000000000)
  dδ := (39157098576481967622253677/500000000000000000000000000)
  dM := (13439535539976035956322153/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(18914338029415718178682937/2500000000000000000000000), (5718326486173824774184027/5000000000000000000000000), (1600272016406992570125567/31250000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21967/42642)
  hi := (10996/21321)
  vmin := (113533700/454585041)
  damping := (113533700/454585041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell087
