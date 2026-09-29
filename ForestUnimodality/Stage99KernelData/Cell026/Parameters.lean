import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18985757981386235492493597/100000000000000000000000000)
  B := (72818927903225638686990351/1000000000000000000000000000)
  C := (-34262801305444540167499667/100000000000000000000000000)
  dδ := (8346805122507854057811727/100000000000000000000000000)
  dM := (10854816479830568711623107/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6986028908752152100092303/1250000000000000000000000), (12263982980980467019094249/500000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4/9)
  hi := (301/666)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell026
