import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 63
  A := (34178745550687104726250709/10000000000000000000000000)
  B := (91524068402826913842113/39062500000000000000000000)
  C := (8387806929006975942275659/25000000000000000000000000)
  dδ := (21559830381620605221915099/250000000000000000000000000)
  dM := (73068911660346383320913111/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10385381452376387656499901/2500000000000000000000000), (27686392126881700370688577/5000000000000000000000000), (21461126531060706668085913/1000000000000000000000000)]
  retention := ![(19/20), (7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99/179)
  hi := (5/9)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell162
