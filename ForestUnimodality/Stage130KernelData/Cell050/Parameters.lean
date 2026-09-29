import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 83
  A := (-7789147237788539240810337/5000000000000000000000000)
  B := (5070101821090289284654773/50000000000000000000000000)
  C := (-24427826378967290414656599/10000000000000000000000000000)
  dδ := (65268030978517979634467849/1000000000000000000000000000)
  dM := (1414661200718004608646583/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6051635108330650769659087/1250000000000000000000000), (23390402050570879843860439/2500000000000000000000000), (33590943198593492979853181/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell050
