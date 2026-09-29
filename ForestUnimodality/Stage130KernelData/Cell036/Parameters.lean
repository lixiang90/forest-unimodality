import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 70
  A := (-787854829762548470313277/500000000000000000000000)
  B := (5799324388778662880961079/50000000000000000000000000)
  C := (-11320521232118284718493051/2500000000000000000000000000)
  dδ := (37534993148641400406706481/500000000000000000000000000)
  dM := (292483827468247243111521/200000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(172294383021619035289973/12500000000000000000000), (1364255198023732695844501/25000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (869/1824)
  hi := (581/1216)
  vmin := (829895/3326976)
  damping := (829895/3326976)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell036
