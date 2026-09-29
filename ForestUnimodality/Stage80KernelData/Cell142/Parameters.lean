import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-6998384275627885841686293/50000000000000000000000000)
  B := (81822743576006468080308309/1000000000000000000000000000)
  C := (3162420447984658038176331/500000000000000000000000000)
  dδ := (11274516824760992539378179/100000000000000000000000000)
  dM := (6891105948752266653623/4000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(61963431597018319152425647/10000000000000000000000000), (15718640130542256283519009/10000000000000000000000000), (33985414814379751646811201/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657/8862)
  hi := (111/211)
  vmin := (11100/44521)
  damping := (11100/44521)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell142
