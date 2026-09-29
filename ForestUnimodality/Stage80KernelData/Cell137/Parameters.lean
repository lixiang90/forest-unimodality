import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 37
  A := (-72280370237022651949132523/1000000000000000000000000000)
  B := (41270254563849265161401547/500000000000000000000000000)
  C := (26589790461501263720001109/5000000000000000000000000000)
  dδ := (11438460487616898542118093/100000000000000000000000000)
  dM := (9485115501881634467867821/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(30899583101332273038508447/5000000000000000000000000), (15319373181356326085733599/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell137
