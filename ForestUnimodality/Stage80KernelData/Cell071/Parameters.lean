import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 36
  A := (4377921595172844679311197/2500000000000000000000000)
  B := (-3411052020108423787903007/400000000000000000000000000)
  C := (-8250098747503164815092491/5000000000000000000000000000)
  dδ := (11006312411844602905386381/100000000000000000000000000)
  dM := (33197364814178514360806793/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3580798220543687793160359/625000000000000000000000), (15956744190415145467909497/500000000000000000000000)]
  retention := ![(4/5), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell071
