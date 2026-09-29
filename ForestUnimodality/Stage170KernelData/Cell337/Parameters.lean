import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell337
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (24)
  A := (11616447091144526950756699 / 250000000000000000000000000)
  B := (17940330023263721670456761 / 1000000000000000000000000000)
  C := (27143191840081265508999309 / 1000000000000000000000000000)
  dδ := (14635439960868027592377771 / 1000000000000000000000000000)
  dM := (6232005523772547186337617 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(17109796074089438366883087 / 5000000000000000000000000), (44288917878995874843894853 / 10000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35 / 52)
  hi := (53 / 78)
  vmin := (1325 / 6084)
  damping := (13250000000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell337
