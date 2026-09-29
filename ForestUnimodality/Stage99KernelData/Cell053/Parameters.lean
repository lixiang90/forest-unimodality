import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 50
  A := (86345357567671394583896927/100000000000000000000000000)
  B := (28065945635824013359993501/1000000000000000000000000000)
  C := (-14032418987193710085970011/10000000000000000000000000000)
  dδ := (93138971912381268714042903/1000000000000000000000000000)
  dM := (40687211721621461624556759/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(58301795343924922576661629/10000000000000000000000000), (2344760304838486408840481/2000000000000000000000000), (747382752482865697629677/40000000000000000000000), (12542299673389811331958299/500000000000000000000000)]
  retention := ![(4/5), (1/2), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4777/9702)
  hi := (3193/6468)
  vmin := (23526725/94128804)
  damping := (23526725/94128804)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell053
