import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (250)
  A := (-1558981241172674826458433 / 1000000000000000000000000)
  B := (46690230828152441688860819 / 1000000000000000000000000000)
  C := (-10763022360569586034773071 / 5000000000000000000000000000)
  dδ := (30550916375855923651227997 / 1000000000000000000000000000)
  dM := (24231158287969185101580483 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(31301053174689347002868089 / 1000000000000000000000000), (21711157727223417168715969 / 100000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 47)
  hi := (9 / 19)
  vmin := (550 / 2209)
  damping := (550 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell126
