import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (62)
  A := (-8237361656612472103233813 / 200000000000000000000000000)
  B := (1256140575651084733549423 / 62500000000000000000000000)
  C := (-36043727998613536711580707 / 500000000000000000000000000)
  dδ := (17738983951330413585401047 / 1000000000000000000000000000)
  dM := (2305921149506404274273641 / 20000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(15388629815663225741673159 / 1000000000000000000000000), (2603751864745239785747799 / 250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell085
