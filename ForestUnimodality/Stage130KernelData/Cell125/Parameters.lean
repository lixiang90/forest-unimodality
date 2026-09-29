import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 73
  A := (-1980202221198000090964797/1000000000000000000000000)
  B := (13248021956123318121356647/100000000000000000000000000)
  C := (46368794918386193118498007/10000000000000000000000000000)
  dδ := (14323910428350705714706237/200000000000000000000000000)
  dM := (16286814237811727927585093/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(512093685904409845477403/31250000000000000000000), (27282913578558840583809797/500000000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell125
