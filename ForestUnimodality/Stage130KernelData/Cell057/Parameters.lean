import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 71
  A := (-18560189631713532210000039/10000000000000000000000000)
  B := (3221864381576436398013641/25000000000000000000000000)
  C := (-12026166872766506227288019/10000000000000000000000000000)
  dδ := (72924044129499751565326449/1000000000000000000000000000)
  dM := (16158452527268423598583169/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12300949141456944957440101/1000000000000000000000000), (1135426409357616535089619/20000000000000000000000)]
  retention := ![(3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell057
