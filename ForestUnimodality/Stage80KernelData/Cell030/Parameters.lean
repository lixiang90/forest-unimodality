import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 101
  A := (1042240434801714115575777/3125000000000000000000000)
  B := (10981551240703303629064891/100000000000000000000000000)
  C := (-15943715057547771518642321/20000000000000000000000000)
  dδ := (19483975247465754043751929/100000000000000000000000000)
  dM := (24855830223517801254307091/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(5012908062110723150794911/500000000000000000000000), (25955463299594892845334471/1000000000000000000000000), (10778195134291356893641023/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/47)
  hi := (1677/3572)
  vmin := (550/2209)
  damping := (550/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell030
