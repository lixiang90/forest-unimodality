import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 30
  A := (8034684624206242770316777/25000000000000000000000000)
  B := (17599476563196367329133807/500000000000000000000000000)
  C := (-169529204133981800661779/1250000000000000000000000)
  dδ := (4930545204425394040237407/100000000000000000000000000)
  dM := (11065378681454690265595353/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(17524344453873252902553759/10000000000000000000000000), (641649191587864931030083/62500000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33/85)
  hi := (101/255)
  vmin := (1716/7225)
  damping := (1716/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell018
