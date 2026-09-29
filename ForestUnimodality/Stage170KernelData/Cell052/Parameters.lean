import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (35)
  A := (8564616866064895195798101 / 50000000000000000000000000)
  B := (13457566933684772525481321 / 1000000000000000000000000000)
  C := (-33477887971901910957317483 / 1000000000000000000000000000)
  dδ := (433448751559917992790677 / 31250000000000000000000000)
  dM := (14626864850423665570869347 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1639582915980510424702743 / 1000000000000000000000000), (16761900362210346848712561 / 2500000000000000000000000), (21349035534331006758179683 / 5000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89 / 255)
  hi := (91 / 255)
  vmin := (14774 / 65025)
  damping := (14774 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell052
