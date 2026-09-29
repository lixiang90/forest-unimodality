import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell197
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-8826794719419142975880277/20000000000000000000000000)
  B := (1335072373611372043011869/10000000000000000000000000)
  C := (1975247327880875980454789/4000000000000000000000000)
  dδ := (13707223500591045328711459/100000000000000000000000000)
  dM := (27332680620390519161955201/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(45659845986992273481064331/10000000000000000000000000), (942658305393111906056447/62500000000000000000000), (9127334477650496102896227/1250000000000000000000000)]
  retention := ![(7/10), (1/4), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97/177)
  hi := (49/89)
  vmin := (1960/7921)
  damping := (1960/7921)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell197
