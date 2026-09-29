import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (20401127193385418345883409/10000000000000000000000000)
  B := (-10492893661066645533130881/500000000000000000000000000)
  C := (-12993065279488834676269171/5000000000000000000000000000)
  dδ := (5607332354978496191666437/50000000000000000000000000)
  dM := (51141700596908580729593741/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63071182439954363019296579/10000000000000000000000000), (68593660313967186326067349/10000000000000000000000000), (5152818081980541364828241/200000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell059
