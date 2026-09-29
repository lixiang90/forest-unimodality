import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 42
  A := (-77257322076544389091168341/1000000000000000000000000000)
  B := (77207340999705956208210011/1000000000000000000000000000)
  C := (21165089557176239819236141/5000000000000000000000000000)
  dδ := (5540547630759037195380401/50000000000000000000000000)
  dM := (8185809763605621279872193/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(878710191083631242392471/125000000000000000000000), (17393246607275330006814329/500000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22597/43472)
  hi := (11311/21736)
  vmin := (117917175/472453696)
  damping := (117917175/472453696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell114
