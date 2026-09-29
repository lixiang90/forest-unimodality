import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-7422896946779952936878999/5000000000000000000000000)
  B := (10775028122978037858903377/100000000000000000000000000)
  C := (30193064889450730442499449/10000000000000000000000000000)
  dδ := (71623167668867518398378991/1000000000000000000000000000)
  dM := (1644136941099341611520479/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(49734308904046633514894893/10000000000000000000000000), (47498830729415448814734191/5000000000000000000000000), (28986814856594630640529431/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/207)
  hi := (7427/14352)
  vmin := (51431975/205979904)
  damping := (51431975/205979904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell097
