import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (14571215584168746183024723/100000000000000000000000000)
  B := (27112299033982299040212993/500000000000000000000000000)
  C := (-10095421297308438974421607/10000000000000000000000000000)
  dδ := (4401391412767827193697201/50000000000000000000000000)
  dM := (629507404268217821662057/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1153678645862896978702139/312500000000000000000000), (54440937672767786281724511/10000000000000000000000000), (44922838435678009716411907/1000000000000000000000000)]
  retention := ![(4/5), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9529/19404)
  hi := (4777/9702)
  vmin := (94098875/376515216)
  damping := (94098875/376515216)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell052
