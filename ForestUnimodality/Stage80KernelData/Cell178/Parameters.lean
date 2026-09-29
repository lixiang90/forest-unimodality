import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 80
  A := (-11134671555178545132491763/10000000000000000000000000)
  B := (20153328028123893012057977/100000000000000000000000000)
  C := (35577301991933141245283423/50000000000000000000000000)
  dδ := (19065673484968403972317219/100000000000000000000000000)
  dM := (20955474963776986145613801/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(11479220141944075361806199/1250000000000000000000000), (12919000496637780273090357/500000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/54)
  hi := (2557/4752)
  vmin := (5612615/22581504)
  damping := (5612615/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell178
