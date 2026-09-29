import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 20
  A := (1260660319627662329189377/10000000000000000000000000)
  B := (16906528717109757520287161/500000000000000000000000000)
  C := (18318045645468152698986941/250000000000000000000000000)
  dδ := (18212099960764557143866327/500000000000000000000000000)
  dM := (8998283549239097928174047/20000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(70005066335862604631756767/10000000000000000000000000)]
  retention := ![(3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41/63)
  hi := (83/126)
  vmin := (3569/15876)
  damping := (35690000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell182
