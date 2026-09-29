import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell410
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (53)
  A := (-2181462504083894153836809 / 4000000000000000000000000)
  B := (47777982943839031326760391 / 1000000000000000000000000000)
  C := (5280448681549678585644969 / 50000000000000000000000000)
  dδ := (1088202011732678498034943 / 40000000000000000000000000)
  dM := (20691286188818748862337793 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10354108976431414035346279 / 500000000000000000000000), (93187480853940518610301069 / 100000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653 / 1128)
  hi := (7 / 12)
  vmin := (35 / 144)
  damping := (35 / 144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell410
