import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell447
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (45)
  A := (-27564913880014242355542819 / 1000000000000000000000000000)
  B := (4504112995163594979075583 / 200000000000000000000000000)
  C := (-33212306659943166553539129 / 500000000000000000000000000)
  dδ := (4812657226586843604854149 / 250000000000000000000000000)
  dM := (15779250570804572101693553 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(8462605323095651055353983 / 2500000000000000000000000), (7339099151445034330265571 / 500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101 / 255)
  hi := (103 / 255)
  vmin := (15554 / 65025)
  damping := (15554 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell447
