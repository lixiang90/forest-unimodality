import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell220
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 29
  A := (-58360974544792847517271639/100000000000000000000000000)
  B := (11421018534875027050645713/100000000000000000000000000)
  C := (18802361244100482262631147/100000000000000000000000000)
  dδ := (71199809613859618706577237/1000000000000000000000000000)
  dM := (10822363757015626174740053/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(70851342516071746935324427/100000000000000000000000000), (10048663407336491104615561/1000000000000000000000000)]
  retention := ![(3/5), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3/5)
  hi := (123/203)
  vmin := (9840/41209)
  damping := (9840/41209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell220
