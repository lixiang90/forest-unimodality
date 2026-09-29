import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-16251234290937279125444093/10000000000000000000000000)
  B := (5746428382778227816896077/50000000000000000000000000)
  C := (5524403238210515328099337/1000000000000000000000000000)
  dδ := (4432724942029181089409029/62500000000000000000000000)
  dM := (14119870827339344680068089/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8625060008381199017080121/1250000000000000000000000), (1686814113547108751056669/312500000000000000000000), (59011634205016299858925777/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97103/182328)
  hi := (57/107)
  vmin := (2850/11449)
  damping := (2850/11449)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell209
