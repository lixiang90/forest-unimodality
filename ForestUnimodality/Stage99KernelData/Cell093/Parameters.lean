import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 61
  A := (-8904937710502393477440819/10000000000000000000000000)
  B := (90907918998387862719035013/1000000000000000000000000000)
  C := (31646114527807403180026391/10000000000000000000000000000)
  dδ := (79409074653337449745116317/1000000000000000000000000000)
  dM := (6394421428518733910989491/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(86493122541516509471648533/10000000000000000000000000), (21150219178754284143906261/1000000000000000000000000), (30233740332843293430187259/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/207)
  hi := (7427/14352)
  vmin := (51431975/205979904)
  damping := (51431975/205979904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell093
