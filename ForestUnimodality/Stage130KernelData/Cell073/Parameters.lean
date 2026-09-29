import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 77
  A := (-12763881023398605984908727/10000000000000000000000000)
  B := (9569685886877785097048843/100000000000000000000000000)
  C := (89356602627256836567787301/100000000000000000000000000000)
  dδ := (7006335200836874554930489/100000000000000000000000000)
  dM := (11425770480453835160200571/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(45346714711274094256054923/5000000000000000000000000), (7244200847972068757485431/5000000000000000000000000), (16624433553843747546352461/1000000000000000000000000), (48511835446080432632243173/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407/808)
  hi := (51/101)
  vmin := (2550/10201)
  damping := (2550/10201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell073
