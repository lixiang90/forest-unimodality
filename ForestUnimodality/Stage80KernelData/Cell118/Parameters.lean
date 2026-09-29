import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-10006697802032975651798097/100000000000000000000000000)
  B := (39407211311202103298789723/500000000000000000000000000)
  C := (907539668791889492238667/200000000000000000000000000)
  dδ := (5543434574545721277294419/50000000000000000000000000)
  dM := (2082733836288304201094651/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8744492783155050075194481/1250000000000000000000000), (13267045691812208829674091/1000000000000000000000000), (4306194422108050190445283/200000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell118
