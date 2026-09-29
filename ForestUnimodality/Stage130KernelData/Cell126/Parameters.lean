import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-3861020474659353332569367/2500000000000000000000000)
  B := (48203185150807084657920143/500000000000000000000000000)
  C := (1532302204358797735606057/400000000000000000000000000)
  dδ := (30987076260686259587817659/500000000000000000000000000)
  dM := (10322094621380117473313787/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12859660107497976611057311/1000000000000000000000000), (9705345519282136734773303/500000000000000000000000), (54127107267063529150163959/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell126
