import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (15276906371195842593380121/10000000000000000000000000)
  B := (35534508213160911904715533/10000000000000000000000000000)
  C := (-3124446862213830404877979/2500000000000000000000000000)
  dδ := (2168567321680497650415731/20000000000000000000000000)
  dM := (15528537452253196940454849/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7119028906664953693095299/1250000000000000000000000), (2695564346614222728248933/500000000000000000000000), (29334170231220035418573389/1000000000000000000000000)]
  retention := ![(4/5), (3/20), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell072
