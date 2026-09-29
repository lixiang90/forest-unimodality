import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 18
  A := (10497195596674225749111997/100000000000000000000000000)
  B := (2422870938519128443389139/125000000000000000000000000)
  C := (-28083349790220007990981799/1000000000000000000000000000)
  dδ := (2410772847740771072932997/125000000000000000000000000)
  dM := (7410236149152882539990067/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(9343755571279280247587451/25000000000000000000000000), (48267193434005672969533407/10000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39/140)
  hi := (2/7)
  vmin := (3939/19600)
  damping := (393900000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell004
