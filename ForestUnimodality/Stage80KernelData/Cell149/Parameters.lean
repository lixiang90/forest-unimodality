import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 39
  A := (4042784953215587104402573/12500000000000000000000000)
  B := (59813554945729596745707113/1000000000000000000000000000)
  C := (3320480575252751035547627/500000000000000000000000000)
  dδ := (5964068247709844450277217/50000000000000000000000000)
  dM := (15178857897146286106554447/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(40995889602821689035039299/100000000000000000000000000), (13932748169270940508113199/2000000000000000000000000), (1696810972347104495838721/100000000000000000000000), (14866349688318830857269859/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94503/178928)
  hi := (28/53)
  vmin := (700/2809)
  damping := (700/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell149
