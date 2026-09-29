import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 43
  A := (17751449309248921826309697/10000000000000000000000000)
  B := (-21277896526058735771069763/5000000000000000000000000000)
  C := (-31308601387606701214882943/10000000000000000000000000000)
  dδ := (1395416352537949371270809/12500000000000000000000000)
  dM := (13477621348161787986907889/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(32897272756907756097177753/5000000000000000000000000), (40267563055920518877428549/5000000000000000000000000), (1501684266014749447037957/50000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell055
