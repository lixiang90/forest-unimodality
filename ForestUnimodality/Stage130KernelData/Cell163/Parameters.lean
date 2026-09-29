import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18696117011757335435362393/10000000000000000000000000)
  B := (6587713054286295499828441/50000000000000000000000000)
  C := (14165428974649322494544501/2500000000000000000000000000)
  dδ := (74210336258770312478638687/1000000000000000000000000000)
  dM := (16820896905831797269598171/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7769168807163341128330103/500000000000000000000000), (10104703303965347060966451/200000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95549/180624)
  hi := (15929/30104)
  vmin := (225793575/906250816)
  damping := (225793575/906250816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell163
