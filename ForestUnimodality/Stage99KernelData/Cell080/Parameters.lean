import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-27437878452271804496476193/50000000000000000000000000)
  B := (10788504914430639691769187/125000000000000000000000000)
  C := (12632016181084318798277799/5000000000000000000000000000)
  dδ := (18198006455628618072140057/200000000000000000000000000)
  dM := (14404425949654205748456937/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63020728339479799018363337/10000000000000000000000000), (17116552612581392711632589/10000000000000000000000000), (2584316294169157313120877/62500000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381/10506)
  hi := (10787/21012)
  vmin := (110297075/441504144)
  damping := (110297075/441504144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell080
