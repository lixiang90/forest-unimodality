import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 107
  A := (2839814810159666852484861/5000000000000000000000000)
  B := (3015365689312470356964191/25000000000000000000000000)
  C := (-94530002710589966508081261/100000000000000000000000000)
  dδ := (23675866638570575162248133/100000000000000000000000000)
  dM := (15489317606960043699482199/5000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(1365340712958898361506499/125000000000000000000000), (3899762305535653439392263/100000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841/1786)
  hi := (1687/3572)
  vmin := (794745/3189796)
  damping := (794745/3189796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell032
