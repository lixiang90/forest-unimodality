import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 24
  A := (73076389879547993700725783/100000000000000000000000000)
  B := (6366255841166327048008533/500000000000000000000000000)
  C := (95047429682631009995041893/1000000000000000000000000000)
  dδ := (5090986039985566542764861/125000000000000000000000000)
  dM := (23790198087416731436219419/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(61024796909637579744867253/100000000000000000000000000), (6498839103644177273011451/5000000000000000000000000), (3918140657630193035565469/1250000000000000000000000), (11113372427657888241725459/2500000000000000000000000)]
  retention := ![(9/10), (4/5), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467/742)
  hi := (236/371)
  vmin := (31860/137641)
  damping := (31860/137641)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell179
