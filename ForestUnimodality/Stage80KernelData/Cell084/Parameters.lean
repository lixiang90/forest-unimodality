import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (96913851261557288797376941/100000000000000000000000000)
  B := (2715567688415055497275219/100000000000000000000000000)
  C := 0
  dδ := (10179269638346134796424991/100000000000000000000000000)
  dM := (1047666246282684615956371/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(710898876183472944179087/156250000000000000000000), (13469966782953459727423251/10000000000000000000000000), (31970606330362706160030939/1000000000000000000000000)]
  retention := ![(4/5), (3/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (395/792)
  hi := (1/2)
  vmin := (156815/627264)
  damping := (156815/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell084
