import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (604504029627412890812721/6250000000000000000000000)
  B := (10484491609244637674858147/500000000000000000000000000)
  C := (-7272559062893661774307219/200000000000000000000000000)
  dδ := (2475267755152065624058011/125000000000000000000000000)
  dM := (4332257354344712699766029/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(14267557609786588046496547/25000000000000000000000000), (16571483904308490497925277/2500000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (20/63)
  hi := (41/126)
  vmin := (860/3969)
  damping := (34400000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell009
