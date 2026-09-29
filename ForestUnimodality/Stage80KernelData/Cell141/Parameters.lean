import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 37
  A := (-16234441779000669257015943/250000000000000000000000000)
  B := (81163657031754696258296633/1000000000000000000000000000)
  C := (11028455029563797099023681/2000000000000000000000000000)
  dδ := (2265921714275154486006869/20000000000000000000000000)
  dM := (3720139484667787151822571/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(62369962638387637099413041/10000000000000000000000000), (30590294110846262043423849/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell141
