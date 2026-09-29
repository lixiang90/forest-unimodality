import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-85628260385587507954596731/1000000000000000000000000000)
  B := (85921063865499275324921769/1000000000000000000000000000)
  C := (14895622445919738923575393/5000000000000000000000000000)
  dδ := (593315178992909891819707/5000000000000000000000000)
  dM := (19473796367146039513335021/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14655960185897125569454147/2500000000000000000000000), (3293631375394616611629317/100000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3493/6868)
  hi := (26/51)
  vmin := (650/2601)
  damping := (650/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell094
