import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-15824636617729263454634747/10000000000000000000000000)
  B := (95325084321795081065964439/1000000000000000000000000000)
  C := (7285938776124444493306753/5000000000000000000000000000)
  dδ := (60405545474699236241367117/1000000000000000000000000000)
  dM := (49638119830256669916951351/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10619573908002841733377863/1000000000000000000000000), (2115561107791849249082361/1000000000000000000000000), (19155865741180900130302689/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3493/6868)
  hi := (26/51)
  vmin := (650/2601)
  damping := (650/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell080
