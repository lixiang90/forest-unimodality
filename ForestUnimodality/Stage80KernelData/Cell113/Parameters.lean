import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-2809440000801042863542989/25000000000000000000000000)
  B := (99911258295718119448736161/1000000000000000000000000000)
  C := (72438292892690906918384819/10000000000000000000000000000)
  dδ := (13171626772654362880210499/100000000000000000000000000)
  dM := (24539678877385784350195763/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55153068474722264369347613/10000000000000000000000000), (65982965323642730481878971/10000000000000000000000000), (23649556581694188395204037/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell113
