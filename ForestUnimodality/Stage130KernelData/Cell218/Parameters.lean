import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 67
  A := (-5205929836920898258423307/6250000000000000000000000)
  B := (629781612447520696904113/7812500000000000000000000)
  C := (22913347288391583411737429/100000000000000000000000000)
  dδ := (2132263543318025644790481/40000000000000000000000000)
  dM := (91534005803503798535253333/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(508336136173306059049537/80000000000000000000000), (4276417572822738044635571/500000000000000000000000), (6877681047295880922831657/500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5/9)
  hi := (116/207)
  vmin := (10556/42849)
  damping := (10556/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell218
