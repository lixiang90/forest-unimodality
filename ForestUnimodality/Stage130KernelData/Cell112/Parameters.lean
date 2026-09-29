import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-15111617893922472577372673/10000000000000000000000000)
  B := (47254591667536767485291449/500000000000000000000000000)
  C := (15887667977006355007202343/5000000000000000000000000000)
  dδ := (61979873873524389538136603/1000000000000000000000000000)
  dM := (10050483451755026862578513/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(814101066599351108621363/62500000000000000000000), (27134780137004415934143253/1000000000000000000000000), (9453929733547123248627031/200000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell112
