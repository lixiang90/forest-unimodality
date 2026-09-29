import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-17072387790401254881089699/10000000000000000000000000)
  B := (11893806999063438745167787/100000000000000000000000000)
  C := (645567151617712302845431/156250000000000000000000000)
  dδ := (8823068976515914887959191/125000000000000000000000000)
  dM := (14630535584834820830163471/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(41454773370527666642715303/10000000000000000000000000), (72343784905842561938627/7812500000000000000000), (28910418247107823930264203/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294/4389)
  hi := (1531/2926)
  vmin := (2135745/8561476)
  damping := (2135745/8561476)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell117
