import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 31
  A := (23256015481407278256753557/100000000000000000000000000)
  B := (3926862644539130114962333/250000000000000000000000000)
  C := (-9313480034376496463632833/200000000000000000000000000)
  dδ := (18847507052236363994657253/1000000000000000000000000000)
  dM := (11379352507899785943920601/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(497251849727379624521717/250000000000000000000000), (94840302016216107006130187/10000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (91/255)
  hi := (31/85)
  vmin := (14924/65025)
  damping := (14924/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell014
