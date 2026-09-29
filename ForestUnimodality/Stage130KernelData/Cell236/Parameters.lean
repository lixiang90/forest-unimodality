import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell236
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 25
  A := (17901293128898399965365229/100000000000000000000000000)
  B := (25582042305418505739877943/1000000000000000000000000000)
  C := (63760168562561780891684293/1000000000000000000000000000)
  dδ := (28703521321407826638605343/1000000000000000000000000000)
  dM := (2638049467448518644457911/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10376330421180185226148751/2000000000000000000000000), (38269654593856885504976617/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/14)
  hi := (41/63)
  vmin := (902/3969)
  damping := (902/3969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell236
