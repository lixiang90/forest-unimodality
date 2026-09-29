import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 63
  A := (-83533511266872111477255203/100000000000000000000000000)
  B := (17035373691747579538713353/200000000000000000000000000)
  C := (22024504257797206194929851/25000000000000000000000000000)
  dδ := (38105505355301938497092351/500000000000000000000000000)
  dM := (11657222784956097153680199/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(22583396136080527427658637/100000000000000000000000000), (16134466720945972895151499/2000000000000000000000000), (9380206732422539772642267/250000000000000000000000), (16275450604923342723395763/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407/808)
  hi := (51/101)
  vmin := (2550/10201)
  damping := (2550/10201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell067
