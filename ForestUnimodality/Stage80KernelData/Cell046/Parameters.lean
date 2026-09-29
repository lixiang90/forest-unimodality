import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 34
  A := (6334997485407849623939569/2500000000000000000000000)
  B := (-3163066472806948942197991/100000000000000000000000000)
  C := (-1636309730951522600772563/400000000000000000000000000)
  dδ := (445638370141497163617883/3125000000000000000000000)
  dM := (77735382895491409328131427/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63019372988859210238388187/10000000000000000000000000), (1880847386947543053992149/62500000000000000000000)]
  retention := ![(4/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47/97)
  hi := (9237/19012)
  vmin := (2350/9409)
  damping := (2350/9409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell046
