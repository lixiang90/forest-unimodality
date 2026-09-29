import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 33
  A := (84491417432788879949612237/100000000000000000000000000)
  B := (824799327849070782955887/15625000000000000000000000)
  C := (36552036649979842940216823/5000000000000000000000000000)
  dδ := (4108902429354004126604849/25000000000000000000000000)
  dM := (2076698240511748189823793/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8443422280092264253781309/1250000000000000000000000), (26933140660409904398875369/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell135
