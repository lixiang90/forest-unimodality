import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell198
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 59
  A := (-36150281138056621465182161/100000000000000000000000000)
  B := (6386549799807331173617797/50000000000000000000000000)
  C := (47348696365010833897457587/100000000000000000000000000)
  dδ := (6721184916968293843186899/50000000000000000000000000)
  dM := (527682483560809167250083/200000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(43175473105778268134713471/10000000000000000000000000), (40798174860607385738831/2500000000000000000000), (49106332043934450837241457/10000000000000000000000000)]
  retention := ![(7/10), (1/4), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/89)
  hi := (99/179)
  vmin := (7920/32041)
  damping := (7920/32041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell198
