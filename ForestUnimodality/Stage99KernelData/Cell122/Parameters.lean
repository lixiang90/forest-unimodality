import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-13573248830168228384707163/20000000000000000000000000)
  B := (95087533873391388850038197/1000000000000000000000000000)
  C := (24841492320263722400064399/5000000000000000000000000000)
  dδ := (91937395518542727734789821/1000000000000000000000000000)
  dM := (15847942945753446322698643/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(73569669940677284714070083/10000000000000000000000000), (10469352866842339011554941/250000000000000000000000)]
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
end ForestUnimodality.Stage99KernelData.Cell122
