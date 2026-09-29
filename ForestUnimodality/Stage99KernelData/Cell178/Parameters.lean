import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 26
  A := (3653279199959886422455213/2500000000000000000000000)
  B := (-3936047178022721720891397/400000000000000000000000000)
  C := (2094317341872075077802151/20000000000000000000000000)
  dδ := (42943937290249416249832137/1000000000000000000000000000)
  dM := (46558802251689976412635241/1000000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10529569837703820489593909/5000000000000000000000000), (18797402563314558054941017/25000000000000000000000000), (57794822589330570039578561/10000000000000000000000000), (24876903013109892270904311/10000000000000000000000000)]
  retention := ![(9/10), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/53)
  hi := (467/742)
  vmin := (128425/550564)
  damping := (128425/550564)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell178
