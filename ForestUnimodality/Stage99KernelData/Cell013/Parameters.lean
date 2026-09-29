import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 26
  A := (26520301418395454296828007/100000000000000000000000000)
  B := (3897815374862383802634369/200000000000000000000000000)
  C := (-27991210628137225269185251/500000000000000000000000000)
  dδ := (24832233333909402295258673/1000000000000000000000000000)
  dM := (18222207724787083788463293/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(460266068233833447465031/400000000000000000000000), (83121645615582195887327543/10000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89/255)
  hi := (91/255)
  vmin := (14774/65025)
  damping := (14774/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell013
