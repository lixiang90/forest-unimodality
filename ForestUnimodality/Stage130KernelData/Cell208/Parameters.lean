import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-17363943023213187954922887/10000000000000000000000000)
  B := (10439410168266477496601397/100000000000000000000000000)
  C := (1795792328527044678931901/400000000000000000000000000)
  dδ := (61650029325622440756760057/1000000000000000000000000000)
  dM := (2792306444811822291156289/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11067084447668346314230803/1000000000000000000000000), (25856587739859269170494827/10000000000000000000000000), (24607875193140646530309823/1000000000000000000000000), (47945836733728853573666129/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/10), (1/20)]
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
end ForestUnimodality.Stage130KernelData.Cell208
