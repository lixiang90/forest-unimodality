import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-15277123430673253301392833/10000000000000000000000000)
  B := (19016745081271935191580269/200000000000000000000000000)
  C := (7852515775090796682628147/2500000000000000000000000000)
  dδ := (61905262118900676593380439/1000000000000000000000000000)
  dM := (2524674121301723086867319/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12770208388078390981945631/1000000000000000000000000), (14760772004540908142189437/200000000000000000000000), (83946499034154553608999549/100000000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311/21736)
  hi := (22647/43472)
  vmin := (471623775/1889814784)
  damping := (471623775/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell110
