import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 32
  A := (19112198543034082277358721/100000000000000000000000000)
  B := (6426864130336357172623707/250000000000000000000000000)
  C := (-42457750567915654438255757/500000000000000000000000000)
  dδ := (7548966099986796456089433/250000000000000000000000000)
  dM := (5366989720715807307693801/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(17574062720074283827642603/10000000000000000000000000), (10742143759653007606402753/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97/255)
  hi := (33/85)
  vmin := (15326/65025)
  damping := (15326/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell017
