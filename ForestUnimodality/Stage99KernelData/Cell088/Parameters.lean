import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-43434985666774455047800529/100000000000000000000000000)
  B := (83735021529079231572545439/1000000000000000000000000000)
  C := (2182018582584350856710953/625000000000000000000000000)
  dδ := (95409327485547701375168117/1000000000000000000000000000)
  dM := (7243746958487405672791337/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(37730285751219638790132649/5000000000000000000000000), (4499489873400305817163769/125000000000000000000000000), (4189168897634772292803973/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10996/21321)
  hi := (7339/14214)
  vmin := (50455625/202037796)
  damping := (50455625/202037796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell088
