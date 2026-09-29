import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (41759631228372484095245909/500000000000000000000000000)
  B := (18434497233256144643753771/250000000000000000000000000)
  C := (4055346623624812526544281/625000000000000000000000000)
  dδ := (5922605281533763199597331/50000000000000000000000000)
  dM := (541549539030572078205511/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(17536182126324599828137707/2500000000000000000000000), (15978546430447018167342321/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791/22366)
  hi := (23607/44732)
  vmin := (498697875/2000951824)
  damping := (498697875/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell145
