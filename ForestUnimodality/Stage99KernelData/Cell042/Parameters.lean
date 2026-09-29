import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 48
  A := (-43225890478270861905230049/5000000000000000000000000000)
  B := (66362756861593291679568551/1000000000000000000000000000)
  C := (-21400253810464268770796803/5000000000000000000000000000)
  dδ := (24251658018612468059593823/250000000000000000000000000)
  dM := (12907244640566106676921043/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(21781793509073152370625337/25000000000000000000000000), (14640778140192518552709089/2500000000000000000000000), (4117105524415205763943959/100000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23/48)
  hi := (2983/6208)
  vmin := (575/2304)
  damping := (575/2304)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell042
