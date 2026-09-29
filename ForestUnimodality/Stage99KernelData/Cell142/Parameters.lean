import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 118
  A := (10443875415982912691958973/100000000000000000000000000)
  B := (5806031284831026512138763/62500000000000000000000000)
  C := (66922356941182026268677419/100000000000000000000000000)
  dδ := (3640045830040562063745213/25000000000000000000000000)
  dM := (3995701626239585410767241/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(3217878614922619284755001/500000000000000000000000), (41902165164570259747733871/10000000000000000000000000), (22557747108221484211298957/1000000000000000000000000), (2161928942234812822675849/100000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31883/60208)
  hi := (47837/90312)
  vmin := (2031876575/8156257344)
  damping := (2031876575/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell142
