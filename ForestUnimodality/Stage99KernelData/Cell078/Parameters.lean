import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-87930508557246305322507851/100000000000000000000000000)
  B := (5154069334137113128635477/50000000000000000000000000)
  C := (11323513489235547367639523/5000000000000000000000000000)
  dδ := (45305514555322057290709381/500000000000000000000000000)
  dM := (16586254622732387285777289/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5024148663740667375421367/2500000000000000000000000), (41221137338218527546018777/5000000000000000000000000), (38778471654874770990772959/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579/7004)
  hi := (5381/10506)
  vmin := (27577625/110376036)
  damping := (27577625/110376036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell078
