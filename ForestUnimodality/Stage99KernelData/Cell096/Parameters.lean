import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 51
  A := (-1610153572939534263852579/2500000000000000000000000)
  B := (92183527758434510857021849/1000000000000000000000000000)
  C := (43256783196445767677995597/10000000000000000000000000000)
  dδ := (45726598103622811963830941/500000000000000000000000000)
  dM := (7600112064915775242704421/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9186952718238087234325917/1250000000000000000000000), (42919258878346113306179177/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11153/21528)
  hi := (22331/43056)
  vmin := (462809975/1853819136)
  damping := (462809975/1853819136)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell096
