import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell513
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-687399896164338338255817 / 312500000000000000000000)
  B := (457998389694150520590199 / 4000000000000000000000000)
  C := (20524296691727000364890987 / 5000000000000000000000000000)
  dδ := (14590926132361637865275661 / 250000000000000000000000000)
  dM := (11235338810005874969621953 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(34732566575004715225816199 / 10000000000000000000000000), (95272814829582543438846187 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657 / 8862)
  hi := (111 / 211)
  vmin := (11100 / 44521)
  damping := (11100 / 44521)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell513
