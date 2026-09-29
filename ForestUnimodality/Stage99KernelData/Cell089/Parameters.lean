import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 61
  A := (-47687550170418349148704351/50000000000000000000000000)
  B := (93893831128765981031136789/1000000000000000000000000000)
  C := (29468519885592712320709907/10000000000000000000000000000)
  dδ := (39459454029289312004813439/500000000000000000000000000)
  dM := (2630221295093590917063553/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(40394379091882512966549257/5000000000000000000000000), (10139635310271788437574969/20000000000000000000000000), (51384429356631521557119413/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10996/21321)
  hi := (7339/14214)
  vmin := (50455625/202037796)
  damping := (50455625/202037796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell089
