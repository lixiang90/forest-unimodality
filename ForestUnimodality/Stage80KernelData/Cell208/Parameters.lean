import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 43
  A := (-2646768256293931067517633/2000000000000000000000000)
  B := (3439328972152638219661469/20000000000000000000000000)
  C := (14604934063002489308402687/50000000000000000000000000)
  dδ := (4461233673663601156933467/50000000000000000000000000)
  dM := (32178235473552035603161947/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(16889897111714311961350177/1000000000000000000000000)]
  retention := ![(3/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21/37)
  hi := (53/93)
  vmin := (2120/8649)
  damping := (2120/8649)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell208
