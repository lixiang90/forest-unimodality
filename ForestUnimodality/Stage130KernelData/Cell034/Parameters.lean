import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 78
  A := (-12966794678929724382498989/10000000000000000000000000)
  B := (48445536505133952875912229/500000000000000000000000000)
  C := (-11579341683744101207387267/2500000000000000000000000000)
  dδ := (70544731956744363698952327/1000000000000000000000000000)
  dM := (11542815566750034596277263/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(74751294750893686469339627/10000000000000000000000000), (28479340025629267252327281/10000000000000000000000000), (13262870811834292794628709/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/19)
  hi := (1733/3648)
  vmin := (90/361)
  damping := (90/361)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell034
