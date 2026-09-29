import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 61
  A := (-93096531442721846104859651/100000000000000000000000000)
  B := (90546752135794578153493717/1000000000000000000000000000)
  C := (5713568918203087597038059/2500000000000000000000000000)
  dδ := (76198126996433482305270957/1000000000000000000000000000)
  dM := (1252578138821485841808423/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(4173396696624242174777919/500000000000000000000000), (12912084648223789429266617/250000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10787/21012)
  hi := (53/103)
  vmin := (2650/10609)
  damping := (2650/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell083
