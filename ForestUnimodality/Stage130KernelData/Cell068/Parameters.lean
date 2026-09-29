import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-3680947188706021169757321/2500000000000000000000000)
  B := (2642040637022879945305931/25000000000000000000000000)
  C := (27153604516609147192726659/100000000000000000000000000000)
  dδ := (17397356915734629723147009/250000000000000000000000000)
  dM := (12769920744791114775029683/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13935843450674518795295853/2500000000000000000000000), (29087569193108100407130223/5000000000000000000000000), (15516615503502093176280141/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/2)
  hi := (405/808)
  vmin := (163215/652864)
  damping := (163215/652864)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell068
