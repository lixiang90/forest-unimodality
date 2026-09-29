import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-68016215366510994865478779/100000000000000000000000000)
  B := (95278727359749612602080049/1000000000000000000000000000)
  C := (50135315382048148066806981/10000000000000000000000000000)
  dδ := (11504953279467414542502901/125000000000000000000000000)
  dM := (15887994033439193589801741/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14743827406230895604721809/2000000000000000000000000), (41860908048522198043883691/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111/211)
  hi := (23557/44732)
  vmin := (498819475/2000951824)
  damping := (498819475/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell124
