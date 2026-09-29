import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell214
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 84
  A := (-13516515147650833183945451/10000000000000000000000000)
  B := (10654404782826558395480987/100000000000000000000000000)
  C := (5835781980925376366542423/20000000000000000000000000)
  dδ := (121455540229468739220689/1953125000000000000000000)
  dM := (12117577769855164462192709/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(34453905109759950242676041/5000000000000000000000000), (23929650962275378134336279/1000000000000000000000000), (7069712933977470026292167/1250000000000000000000000)]
  retention := ![(7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell214
