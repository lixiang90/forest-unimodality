import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell212
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 42
  A := (-5207413521263913552772351/5000000000000000000000000)
  B := (934046449047296750700653/6250000000000000000000000)
  C := (6998125940007886292004713/25000000000000000000000000)
  dδ := (86274660779018491618685971/1000000000000000000000000000)
  dM := (3470141918121010687382777/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(919987176047719068527897/625000000000000000000000), (7592432122363453217417373/500000000000000000000000)]
  retention := ![(2/5), (7/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/93)
  hi := (107/187)
  vmin := (8560/34969)
  damping := (8560/34969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell212
