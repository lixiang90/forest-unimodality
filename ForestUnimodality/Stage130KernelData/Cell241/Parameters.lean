import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell241
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (904853015717567148223921/6250000000000000000000000)
  B := (6014840360739485622398881/250000000000000000000000000)
  C := (4110303142767086220787931/100000000000000000000000000)
  dδ := (25028790899966499305939749/1000000000000000000000000000)
  dM := (771295793634672825615263/3125000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(24027872140141495194143317/10000000000000000000000000), (18828055179582541267535589/5000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/78)
  hi := (107/156)
  vmin := (5243/24336)
  damping := (13107500000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell241
