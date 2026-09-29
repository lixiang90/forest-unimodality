import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 34
  A := (6841125517304097958692921/50000000000000000000000000)
  B := (5806658650702027635315261/200000000000000000000000000)
  C := (-23748892772947657880955319/250000000000000000000000000)
  dδ := (31995678007235087147996921/1000000000000000000000000000)
  dM := (31226191755588542185023693/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(18827970116681609358266769/10000000000000000000000000), (5796855458077063261157491/500000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/85)
  hi := (101/255)
  vmin := (1716/7225)
  damping := (1716/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell018
