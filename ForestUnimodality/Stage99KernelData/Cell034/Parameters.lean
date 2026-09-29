import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 49
  A := (-14214543453475384959716621/10000000000000000000000000)
  B := (3528867685663984038457741/25000000000000000000000000)
  C := (-11652488096460243346963459/2000000000000000000000000000)
  dδ := (94795183502160526578528277/1000000000000000000000000000)
  dM := (11571924529174830616196079/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(58757411274441571080728863/10000000000000000000000000), (20497548278640369545655631/10000000000000000000000000), (39564090759885971237963531/1000000000000000000000000)]
  retention := ![(3/5), (1/2), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/19)
  hi := (1733/3648)
  vmin := (90/361)
  damping := (90/361)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell034
