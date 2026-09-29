import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (48)
  A := (911044079152791058717753 / 5000000000000000000000000)
  B := (1283250593205136373328723 / 125000000000000000000000000)
  C := (-32037655310550854081963479 / 1000000000000000000000000000)
  dδ := (10716165058709424193206239 / 1000000000000000000000000000)
  dM := (8726817699092086677483543 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(5004832801475726000717259 / 200000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 51)
  hi := (97 / 255)
  vmin := (608 / 2601)
  damping := (608 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell065
