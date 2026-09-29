import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 56
  A := (1499830830136269485652889/12500000000000000000000000)
  B := (53266646733783722111876813/1000000000000000000000000000)
  C := (-10317508871861588541640753/20000000000000000000000000000)
  dδ := (42197066679102251951505309/500000000000000000000000000)
  dM := (47679334387229705197186469/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8346855505708994371616427/2000000000000000000000000), (5650813904629026218628951/1250000000000000000000000), (3176861331075544825353063/200000000000000000000000), (6291546535304302523172737/200000000000000000000000)]
  retention := ![(4/5), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/99)
  hi := (131/264)
  vmin := (2450/9801)
  damping := (2450/9801)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell056
