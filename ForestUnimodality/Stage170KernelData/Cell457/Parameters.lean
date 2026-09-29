import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell457
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (125)
  A := (-436998992823112861970003 / 200000000000000000000000)
  B := (6004074789139866169529469 / 50000000000000000000000000)
  C := (-35513726446796167746100537 / 100000000000000000000000000)
  dδ := (31505791537359176257560023 / 500000000000000000000000000)
  dM := (2272034406693232075347133 / 2000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(9079549614093334497511023 / 500000000000000000000000), (37748405258022657449146209 / 1000000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613 / 3478)
  hi := (22 / 47)
  vmin := (3008245 / 12096484)
  damping := (3008245 / 12096484)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell457
