import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 113
  A := (29639185710494334536235783/50000000000000000000000000)
  B := (6230890709774089541994613/50000000000000000000000000)
  C := (-5017849739131069464193047/5000000000000000000000000)
  dδ := (24911654334004257327350729/100000000000000000000000000)
  dM := (32216876565822269440353409/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2921496160388326934764791/250000000000000000000000), (41180438370963997840590309/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1687/3572)
  hi := (9/19)
  vmin := (3179995/12759184)
  damping := (3179995/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell035
