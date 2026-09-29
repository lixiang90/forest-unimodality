import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell192
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 63
  A := (-25723503710062741777875317/50000000000000000000000000)
  B := (2923947989012913306616781/20000000000000000000000000)
  C := (13444670765347033203340743/25000000000000000000000000)
  dδ := (7539293901530023933599267/50000000000000000000000000)
  dM := (31072828613601991519510559/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(4706079256042503544676947/1250000000000000000000000), (77842248770898403442686231/100000000000000000000000000), (22890044960974918808460643/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell192
