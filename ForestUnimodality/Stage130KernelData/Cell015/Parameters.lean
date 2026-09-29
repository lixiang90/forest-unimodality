import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 33
  A := (4525644481854574047385853/25000000000000000000000000)
  B := (2165458715877869883686957/125000000000000000000000000)
  C := (-1990160792523124055897199/40000000000000000000000000)
  dδ := (18909869968082089475291951/1000000000000000000000000000)
  dM := (12647556810002960874655953/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(10751377655006741917986801/5000000000000000000000000), (10256214005626400620485583/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31/85)
  hi := (19/51)
  vmin := (1674/7225)
  damping := (1674/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell015
