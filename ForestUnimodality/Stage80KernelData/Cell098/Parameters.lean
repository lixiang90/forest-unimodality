import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-29855270440426300403657933/100000000000000000000000000)
  B := (10154811534961385999231709/100000000000000000000000000)
  C := (787263269361903640641831/200000000000000000000000000)
  dδ := (11872257936643638986939919/100000000000000000000000000)
  dM := (22415837344011489522255243/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11116108914155772069420891/2000000000000000000000000), (2595728332462694964988259/400000000000000000000000), (13269647872170740043884507/500000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10787/21012)
  hi := (53/103)
  vmin := (2650/10609)
  damping := (2650/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell098
