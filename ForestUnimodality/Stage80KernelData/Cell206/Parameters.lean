import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell206
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 47
  A := (-2497862581463952438269871/2000000000000000000000000)
  B := (7904242077574200053824427/50000000000000000000000000)
  C := (2937113454201839002344343/10000000000000000000000000)
  dδ := (42851437373414083542577657/500000000000000000000000000)
  dM := (1744374760177151782291477/625000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(22741086043988998355303011/10000000000000000000000000), (8266169246690040495195717/500000000000000000000000)]
  retention := ![(2/5), (7/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell206
