import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 53
  A := (-22869116759917696981574409/1000000000000000000000000000)
  B := (31124952859304784447136427/500000000000000000000000000)
  C := (-21492686022113365387764539/10000000000000000000000000000)
  dδ := (2215523736063955764774569/25000000000000000000000000)
  dM := (2789711405122529113559393/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14799732491791550703652547/5000000000000000000000000), (64431531843698959249877589/10000000000000000000000000), (21743784759834547060108889/500000000000000000000000)]
  retention := ![(4/5), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell049
