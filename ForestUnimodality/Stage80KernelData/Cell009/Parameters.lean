import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (20993737210205770384874313/250000000000000000000000000)
  B := (14193320546921191216416247/500000000000000000000000000)
  C := (-6019931333239664228429433/125000000000000000000000000)
  dδ := (26924407484554144232014039/1000000000000000000000000000)
  dM := (7694878324350547661551747/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(32006573473839206034341487/100000000000000000000000000), (58713750384919505265202133/10000000000000000000000000)]
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
end ForestUnimodality.Stage80KernelData.Cell009
