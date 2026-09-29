import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 84
  A := (-6139329401957628001795797/5000000000000000000000000)
  B := (21907430104271995857656563/250000000000000000000000000)
  C := (1097826372619109709660723/1000000000000000000000000000)
  dδ := (13245254670743086822248813/200000000000000000000000000)
  dM := (2456717087688057850163037/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11863139396653648915958001/1000000000000000000000000), (14168775255195185991397011/200000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10429/20604)
  hi := (5227/10302)
  vmin := (26527025/106131204)
  damping := (26527025/106131204)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell076
