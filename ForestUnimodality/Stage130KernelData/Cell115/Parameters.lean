import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-1025275399211910507668577/625000000000000000000000)
  B := (1447057489336767838183917/12500000000000000000000000)
  C := (19461438443495512190528629/5000000000000000000000000000)
  dδ := (8818002992077113300073421/125000000000000000000000000)
  dM := (890715638398315018428239/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12874737214470644008912359/2500000000000000000000000), (75075151273143667651766009/10000000000000000000000000), (58635507611910206549055147/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583/8778)
  hi := (2294/4389)
  vmin := (4805930/19263321)
  damping := (4805930/19263321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell115
