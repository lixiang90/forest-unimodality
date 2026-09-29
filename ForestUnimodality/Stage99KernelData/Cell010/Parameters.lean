import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 23
  A := (11138295921844549752677267/100000000000000000000000000)
  B := (4048951795642323492341319/200000000000000000000000000)
  C := (-7575500486399158739381221/200000000000000000000000000)
  dδ := (1956998543574065690942021/100000000000000000000000000)
  dM := (4174465556568121349162101/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(44794915838539950403429657/50000000000000000000000000), (68247138212465756623714697/10000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
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
end ForestUnimodality.Stage99KernelData.Cell010
