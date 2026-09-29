import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (4517983102684512661824101/2000000000000000000000000)
  B := (-10018453028705440882584199/500000000000000000000000000)
  C := (-31273899367727678137718339/5000000000000000000000000000)
  dδ := (1248760446016256991930149/10000000000000000000000000)
  dM := (17416115511163419125872931/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6803479671815117590938371/1000000000000000000000000), (5619715586063598777855077/250000000000000000000000), (5929019135271330398495593/500000000000000000000000)]
  retention := ![(4/5), (1/20), (1/100)]
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
end ForestUnimodality.Stage80KernelData.Cell042
