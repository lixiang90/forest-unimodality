import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell232
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 31
  A := (-16163176798596015137476911/50000000000000000000000000)
  B := (52548442029011294129858811/1000000000000000000000000000)
  C := (83467476669614862339052763/1000000000000000000000000000)
  dδ := (7773658671739512235343561/250000000000000000000000000)
  dM := (60931784292670115692203137/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8812341536309304945717713/2500000000000000000000000), (39516382231406348424229691/5000000000000000000000000)]
  retention := ![(3/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129/209)
  hi := (33/53)
  vmin := (660/2809)
  damping := (660/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell232
