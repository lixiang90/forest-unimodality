import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (152)
  A := (-42216351097701695415764789 / 50000000000000000000000000)
  B := (34804140859530256768561429 / 1000000000000000000000000000)
  C := (-4194737670513252331128129 / 25000000000000000000000000)
  dδ := (3070459719399260857530809 / 125000000000000000000000000)
  dM := (17332881964254900062673281 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(8926280011486621646099593 / 500000000000000000000000), (51604156774510649086096237 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17 / 37)
  hi := (1613 / 3478)
  vmin := (340 / 1369)
  damping := (340 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell117
