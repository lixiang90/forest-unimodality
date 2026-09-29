import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 121
  A := (254290861330263737194457/2500000000000000000000000)
  B := (47314013611257699221113171/500000000000000000000000000)
  C := (68711062843479453476902563/100000000000000000000000000)
  dδ := (927479372123850114018051/6250000000000000000000000)
  dM := (16352011780776146924326619/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(67554801281717251626446341/10000000000000000000000000), (20267214109682285538838187/5000000000000000000000000), (25248902213005465000605909/1000000000000000000000000), (20233623058865088495394957/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31833/60208)
  hi := (23881/45156)
  vmin := (508068275/2039064336)
  damping := (508068275/2039064336)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell136
