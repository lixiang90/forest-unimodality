import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 51
  A := (-1317273998320929708754079/2000000000000000000000000)
  B := (93206433307613745231634539/1000000000000000000000000000)
  C := (43683099632262339245825089/10000000000000000000000000000)
  dδ := (18322524704255174765599179/200000000000000000000000000)
  dM := (15370389623992036353533619/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(36682161087447475722456147/5000000000000000000000000), (42917696469791991376041551/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell098
