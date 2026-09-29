import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 37
  A := (11948750075713744257299709/100000000000000000000000000)
  B := (31601831834987624547661511/1000000000000000000000000000)
  C := (-2734381059536310915047963/25000000000000000000000000)
  dδ := (34927927772441025311422891/1000000000000000000000000000)
  dM := (873057611521484627304171/2500000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(5570184784603151584292391/2500000000000000000000000), (3173054613994417127997849/250000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101/255)
  hi := (103/255)
  vmin := (15554/65025)
  damping := (15554/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell019
