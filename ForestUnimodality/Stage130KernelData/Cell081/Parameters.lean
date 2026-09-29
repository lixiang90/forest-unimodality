import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-11797332675092423903606687/10000000000000000000000000)
  B := (18521083509884317397364839/200000000000000000000000000)
  C := (10519163895041459128032457/5000000000000000000000000000)
  dδ := (2229586357675440461828531/31250000000000000000000000)
  dM := (560680973507697989581533/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5093379377526358275929397/500000000000000000000000), (42615421425107730124537397/100000000000000000000000000), (64138120832520357339490147/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26/51)
  hi := (3579/7004)
  vmin := (12258075/49056016)
  damping := (12258075/49056016)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell081
