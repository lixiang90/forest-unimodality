import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (-12342543124822835802767429/125000000000000000000000000)
  B := (2688528699849077920058793/31250000000000000000000000)
  C := (80151482628205705793789093/10000000000000000000000000000)
  dδ := (11581929433669788109817489/100000000000000000000000000)
  dM := (10186556191286340322665893/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(27418519389377258299589357/5000000000000000000000000), (9301625295619903255328609/500000000000000000000000), (97065110398141261072169073/10000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11/21)
  hi := (1549/2954)
  vmin := (2176345/8726116)
  damping := (2176345/8726116)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell128
