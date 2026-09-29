import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell224
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 23
  A := (10121786618493760262538217/5000000000000000000000000)
  B := (-6739155903436115126192707/250000000000000000000000000)
  C := (13918656270859819379381861/100000000000000000000000000)
  dδ := (61139759437045110290753769/1000000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(12093697737146775761374329/5000000000000000000000000), (1555940509384719921959217/1562500000000000000000000), (70887448111363990932431989/10000000000000000000000000)]
  retention := ![(9/10), (7/10), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/53)
  hi := (467/742)
  vmin := (128425/550564)
  damping := (128425/550564)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell224
