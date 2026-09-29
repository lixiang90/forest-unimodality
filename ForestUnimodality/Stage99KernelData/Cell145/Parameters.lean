import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 116
  A := (11207681479554605253667887/100000000000000000000000000)
  B := (45627067167681230330789077/500000000000000000000000000)
  C := (8215901692448360216225467/12500000000000000000000000)
  dδ := (3588441074254664076015331/25000000000000000000000000)
  dM := (15675924152617167536133413/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(31388670327573295892875649/5000000000000000000000000), (5263187080655109539861769/1250000000000000000000000), (664762871160167412298847/31250000000000000000000), (2759362141852428340627057/125000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7977/15052)
  hi := (95749/180624)
  vmin := (8126696375/32625029376)
  damping := (8126696375/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell145
