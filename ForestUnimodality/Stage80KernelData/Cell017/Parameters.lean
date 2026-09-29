import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 28
  A := (1894198293429195365078499/12500000000000000000000000)
  B := (40523591156509858324241691/1000000000000000000000000000)
  C := (-12090717385126430183373003/100000000000000000000000000)
  dδ := (11497234537712010607468649/250000000000000000000000000)
  dM := (29287932588055741499680207/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(49651613107485487175196681/100000000000000000000000000), (49080496980145538188367027/50000000000000000000000000), (23442779790245666937664737/2500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell017
