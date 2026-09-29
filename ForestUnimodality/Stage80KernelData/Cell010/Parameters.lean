import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 20
  A := (32096629899793537870067439/500000000000000000000000000)
  B := (29985243710924126825378977/1000000000000000000000000000)
  C := (-3254407825194066683494043/62500000000000000000000000)
  dδ := (6904758641980800540349783/250000000000000000000000000)
  dM := (16495873254665415689849961/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(1619398666514820089856741/6250000000000000000000000), (3995047862533000482265777/625000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41/126)
  hi := (1/3)
  vmin := (3485/15876)
  damping := (34850000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell010
