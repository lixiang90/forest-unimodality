import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 89
  A := (-441169488034075775795273/312500000000000000000000)
  B := (11347642562266519600244763/125000000000000000000000000)
  C := (39827283759362470255682709/10000000000000000000000000000)
  dδ := (15796824013493020177900661/250000000000000000000000000)
  dM := (96689839344050814394504467/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14118050376593620498510973/1000000000000000000000000), (18352753173509295692156229/250000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531/2926)
  hi := (11/21)
  vmin := (110/441)
  damping := (110/441)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell120
