import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 115
  A := (19809363708344347344336711/100000000000000000000000000)
  B := (84625814105389524089062547/1000000000000000000000000000)
  C := (63681225412870323676628459/100000000000000000000000000)
  dδ := (693131485308501188447039/5000000000000000000000000)
  dM := (14496370694970482379676513/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(70060366529142514835371003/10000000000000000000000000), (13142647854496765091880661/5000000000000000000000000), (11669774035038442405731729/12500000000000000000000000), (22516224691734851859337141/1000000000000000000000000), (20344819619319480352714891/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31933/60208)
  hi := (113/213)
  vmin := (11300/45369)
  damping := (11300/45369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell148
