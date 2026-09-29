import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 17
  A := (19125020026280868954415837/1000000000000000000000000000)
  B := (15460576739422002973123327/500000000000000000000000000)
  C := (-10053247218725207615119821/250000000000000000000000000)
  dδ := (2689551721414151774780521/100000000000000000000000000)
  dM := (31764555194825768672656219/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(49440900060007306748843803/10000000000000000000000000)]
  retention := ![(1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/7)
  hi := (37/126)
  vmin := (10/49)
  damping := (400000000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell005
