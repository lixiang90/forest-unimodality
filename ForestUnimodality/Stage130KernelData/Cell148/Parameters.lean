import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18668754547018328493379613/10000000000000000000000000)
  B := (13067955004558184928242781/100000000000000000000000000)
  C := (10598208610116182856741851/2000000000000000000000000000)
  dδ := (73113821042481610956720317/1000000000000000000000000000)
  dM := (16604904112317690496186673/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1934176408826353332770509/125000000000000000000000), (12647977139487476705426161/250000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28/53)
  hi := (95449/180624)
  vmin := (8129868575/32625029376)
  damping := (8129868575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell148
