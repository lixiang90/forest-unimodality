import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 90
  A := (-7858171515354903330319303/5000000000000000000000000)
  B := (96806991501553196766138853/1000000000000000000000000000)
  C := (14539585388576054415105121/5000000000000000000000000000)
  dδ := (3860259282543151634903289/62500000000000000000000000)
  dM := (5130095942211473653699061/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12489043343194499158244071/1000000000000000000000000), (75880476122291540264086507/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7427/14352)
  hi := (11153/21528)
  vmin := (115712375/463454784)
  damping := (115712375/463454784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell100
