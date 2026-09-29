import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 62
  A := (-38011612732522242041000027/100000000000000000000000000)
  B := (25346988395327681165003497/500000000000000000000000000)
  C := (-8652843488654474168875197/50000000000000000000000000)
  dδ := (8186730417303041129617469/200000000000000000000000000)
  dM := (1580767679341210128827859/3125000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(22543255152583951961275943/5000000000000000000000000), (2755947389710500683435157/125000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/51)
  hi := (67/153)
  vmin := (638/2601)
  damping := (638/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell024
