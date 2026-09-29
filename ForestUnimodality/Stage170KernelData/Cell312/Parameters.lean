import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell312
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (43)
  A := (33573311579587715733907771 / 1000000000000000000000000000)
  B := (1664981385726020191376251 / 125000000000000000000000000)
  C := (3833581847310939694911669 / 125000000000000000000000000)
  dδ := (530909003445318317809809 / 50000000000000000000000000)
  dM := (31417100261797536011124099 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(18446271703497219007772401 / 5000000000000000000000000), (3132364307593128227580337 / 250000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 53)
  hi := (467 / 742)
  vmin := (128425 / 550564)
  damping := (128425 / 550564)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell312
