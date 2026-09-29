import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 44
  A := (5621073799936791343156983/5000000000000000000000000)
  B := (1401676874459465696118321/62500000000000000000000000)
  C := (-11615051862089898371700053/25000000000000000000000000000)
  dδ := (10506519415298908037836867/100000000000000000000000000)
  dM := (92263262183416917035921889/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(27680460392357519872064131/5000000000000000000000000), (333826011598494432064399/200000000000000000000000), (37814402031444849683339271/1000000000000000000000000)]
  retention := ![(4/5), (2/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (131/264)
  hi := (197/396)
  vmin := (17423/69696)
  damping := (17423/69696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell080
