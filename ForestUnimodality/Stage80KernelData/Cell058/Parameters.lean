import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (2446105288397884074136357/1250000000000000000000000)
  B := (-18548102757276297564148493/1000000000000000000000000000)
  C := (-25527791259443441754251047/10000000000000000000000000000)
  dδ := (10963302111063225052767223/100000000000000000000000000)
  dM := (53050851399498032308355011/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15208361977584203827973397/2500000000000000000000000), (79786640817799652225517093/10000000000000000000000000), (5946951278979994093276673/250000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell058
