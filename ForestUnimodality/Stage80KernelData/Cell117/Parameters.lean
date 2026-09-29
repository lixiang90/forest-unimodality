import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-501533247411429088344903/4000000000000000000000000)
  B := (2531325465997270526830043/25000000000000000000000000)
  C := (72178877145675267648639029/10000000000000000000000000000)
  dδ := (2631429238570258122287271/20000000000000000000000000)
  dM := (497437922483908497722771/200000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55629633702287639707151357/10000000000000000000000000), (38435212292390925625795717/10000000000000000000000000), (13171894257232462877027501/500000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell117
