import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 60
  A := (-29421989870169548197509357/50000000000000000000000000)
  B := (78962502296453504491147157/1000000000000000000000000000)
  C := (3744326536073148731405269/625000000000000000000000000)
  dδ := (4012519964729108212786457/50000000000000000000000000)
  dM := (2899668144870566383226873/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1841508428532728114390693/1000000000000000000000000), (621308173082193704317433/100000000000000000000000), (48512459482648830899620407/5000000000000000000000000), (20790114334937626949795231/500000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557/44732)
  hi := (11791/22366)
  vmin := (124689825/500237956)
  damping := (124689825/500237956)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell127
