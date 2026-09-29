import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 89
  A := (-14978688139913886490006689/10000000000000000000000000)
  B := (94007617393403727912293277/1000000000000000000000000000)
  C := (3197836377900183275901913/1000000000000000000000000000)
  dδ := (6188768675168482974457973/100000000000000000000000000)
  dM := (10009178430036645267992013/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13277325237110149558361627/1000000000000000000000000), (74166126098524657095367729/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell114
