import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-3512367125368580117239503/25000000000000000000000000)
  B := (1020787660225930121304927/10000000000000000000000000)
  C := (7344433740479075663210029/1000000000000000000000000000)
  dδ := (13111487055228376874538299/100000000000000000000000000)
  dM := (12492252107353615277196557/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55635907393972789947156343/10000000000000000000000000), (29965982279757623629734553/10000000000000000000000000), (849236122212512878348889/31250000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell119
