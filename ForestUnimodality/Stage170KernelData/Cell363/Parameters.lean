import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell363
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (35)
  A := (18222412141608014147564631 / 100000000000000000000000000)
  B := (3084621478352733356387283 / 200000000000000000000000000)
  C := (-517075990992664404760637 / 12500000000000000000000000)
  dδ := (8193064011664965770598279 / 500000000000000000000000000)
  dM := (47977982254734687355291617 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10017322028679884748925133 / 5000000000000000000000000), (10885723390712263025648099 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (91 / 255)
  hi := (31 / 85)
  vmin := (14924 / 65025)
  damping := (14924 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell363
