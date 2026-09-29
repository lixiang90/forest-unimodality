import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-3282776928333463886104937/2000000000000000000000000)
  B := (5781228553060674402175323/50000000000000000000000000)
  C := (6892837936044171609495379/1250000000000000000000000000)
  dδ := (35443327168352627143388389/500000000000000000000000000)
  dM := (2839052462282721112779571/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(33266274191643656621408809/5000000000000000000000000), (57242049636678000723577497/10000000000000000000000000), (14728947337404575179675703/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (48539/91164)
  hi := (97103/182328)
  vmin := (8275603175/33243499584)
  damping := (8275603175/33243499584)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell207
