import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (171)
  A := (-1153261955588270316610533 / 1000000000000000000000000)
  B := (8284933823639803462945963 / 200000000000000000000000000)
  C := (-19454844451581984610122333 / 100000000000000000000000000)
  dδ := (27171347774357850618498489 / 1000000000000000000000000000)
  dM := (20770906589507462055611831 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(8597612516947599203831487 / 500000000000000000000000), (30736178204857818485606913 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell121
