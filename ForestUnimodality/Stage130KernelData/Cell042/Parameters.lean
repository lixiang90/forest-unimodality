import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 84
  A := (-1803466280039654119615733/1250000000000000000000000)
  B := (96497428483203917526367377/1000000000000000000000000000)
  C := (-7290643583592863350914537/2500000000000000000000000000)
  dδ := (16256807899967067737589943/250000000000000000000000000)
  dM := (2154731217977818094611031/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(81150821264016794742701677/10000000000000000000000000), (6335404798673076598447551/2000000000000000000000000), (71212341476029834552718967/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2983/6208)
  hi := (4487/9312)
  vmin := (9620175/38539264)
  damping := (9620175/38539264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell042
