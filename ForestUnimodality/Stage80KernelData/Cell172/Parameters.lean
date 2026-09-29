import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell172
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 96
  A := (3253107171422407543914801/1250000000000000000000000)
  B := (-85655036190412231489332839/100000000000000000000000000000)
  C := (78167081726551168596728303/100000000000000000000000000)
  dδ := (491033526897593983195911/2500000000000000000000000)
  dM := (5372423699282418514330817/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(46560712171567937289751171/5000000000000000000000000), (18148689672788287374771699/10000000000000000000000000), (8842594070581700549382731/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97103/182328)
  hi := (57/107)
  vmin := (2850/11449)
  damping := (2850/11449)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell172
