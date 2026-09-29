import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell505
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-9581139232605268790621267 / 5000000000000000000000000)
  B := (5135750334679924089531511 / 50000000000000000000000000)
  C := (28504479920924848633523307 / 10000000000000000000000000000)
  dδ := (58036360991195412584175983 / 1000000000000000000000000000)
  dM := (5005684592098749415359227 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(47898954492560239515341891 / 5000000000000000000000000), (22612201335491949549805213 / 250000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647 / 43472)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell505
