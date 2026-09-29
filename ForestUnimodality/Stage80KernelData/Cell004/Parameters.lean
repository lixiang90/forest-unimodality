import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 16
  A := (5141838681248813493596117/200000000000000000000000000)
  B := (29465873039674888439476419/1000000000000000000000000000)
  C := (-7472588251689132876620647/200000000000000000000000000)
  dδ := (208987918990626270199229/8000000000000000000000000)
  dM := (2966420517289432962591833/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(354192291695511127236351/78125000000000000000000)]
  retention := ![(1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39/140)
  hi := (2/7)
  vmin := (3939/19600)
  damping := (393900000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell004
