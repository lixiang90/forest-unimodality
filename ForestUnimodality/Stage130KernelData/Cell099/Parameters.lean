import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-7734275066452458108301471/5000000000000000000000000)
  B := (1384592118767722333794179/12500000000000000000000000)
  C := (29948335322645914732819783/10000000000000000000000000000)
  dδ := (71707551320767545788292807/1000000000000000000000000000)
  dM := (3380063334552958352781371/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(40151034133596281705536057/10000000000000000000000000), (2805976107468798108612873/250000000000000000000000), (3571589651605386883659321/62500000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell099
