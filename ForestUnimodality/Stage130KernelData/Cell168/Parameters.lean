import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-3251060078292557922168271/2000000000000000000000000)
  B := (10037576564728900585521387/100000000000000000000000000)
  C := (48131403707406912248489839/10000000000000000000000000000)
  dδ := (31448311031585358954476561/500000000000000000000000000)
  dM := (2692091741931763393749777/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(606647475916213263502641/50000000000000000000000), (1058078119009476791845259/1000000000000000000000000), (36562684420918657224319759/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (15929/30104)
  hi := (95599/180624)
  vmin := (8128304975/32625029376)
  damping := (8128304975/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell168
