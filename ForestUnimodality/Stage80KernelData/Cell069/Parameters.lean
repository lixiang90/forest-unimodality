import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (955785027501570715884327/500000000000000000000000)
  B := (-3108069568574702706831303/250000000000000000000000000)
  C := (-19005432968821484029930957/10000000000000000000000000000)
  dδ := (5818667348820077273030549/50000000000000000000000000)
  dM := (6505934363893423966543339/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6115530080544194113656431/1000000000000000000000000), (32621882466679664958064677/1000000000000000000000000), (5298473520498774291809241/5000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9529/19404)
  hi := (4777/9702)
  vmin := (94098875/376515216)
  damping := (94098875/376515216)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell069
