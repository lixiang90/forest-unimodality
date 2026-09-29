import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell171
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 96
  A := (26213607429093866529967727/10000000000000000000000000)
  B := (-799328761547010713250927/400000000000000000000000000)
  C := (78218363209363228616410879/100000000000000000000000000)
  dδ := (19637944925670902662773187/100000000000000000000000000)
  dM := (10592904212987322865729967/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(3747951992963127310076743/400000000000000000000000), (17717887780496435201627037/10000000000000000000000000), (35387278166601127793455817/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (48539/91164)
  hi := (97103/182328)
  vmin := (8275603175/33243499584)
  damping := (8275603175/33243499584)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell171
