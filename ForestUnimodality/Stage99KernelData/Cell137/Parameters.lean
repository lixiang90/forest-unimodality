import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 121
  A := (10094409508718389268722149/100000000000000000000000000)
  B := (9478492757578517446948041/100000000000000000000000000)
  C := (68679138499855374444535983/100000000000000000000000000)
  dδ := (7424416732850504241358891/50000000000000000000000000)
  dM := (8180623132628318415135449/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(33640777532808057159741111/5000000000000000000000000), (40924172065615671556315647/10000000000000000000000000), (2494349665962383255646273/100000000000000000000000), (820403468421669685994857/40000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881/45156)
  hi := (95549/180624)
  vmin := (8128831175/32625029376)
  damping := (8128831175/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell137
