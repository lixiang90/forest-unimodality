import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 17
  A := (24913283336709088069405027/250000000000000000000000000)
  B := (19090221367802730212392959/1000000000000000000000000000)
  C := (-6345339546292206971134231/250000000000000000000000000)
  dδ := (60814593426862376731451/3125000000000000000000000)
  dM := (55050904611946059694777/400000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(4537502676781207666678597/50000000000000000000000000), (29231866364983954964529289/50000000000000000000000000), (19361454336446610735578133/5000000000000000000000000)]
  retention := ![(3/5), (1/2), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/35)
  hi := (37/140)
  vmin := (234/1225)
  damping := (374400000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell001
