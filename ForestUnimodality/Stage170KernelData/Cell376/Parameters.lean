import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell376
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-640968300763645493773879 / 500000000000000000000000)
  B := (373319376580178372004859 / 5000000000000000000000000)
  C := (-23947593210914319694637697 / 100000000000000000000000000)
  dδ := (8844308184375601622484453 / 200000000000000000000000000)
  dM := (15984609450362424645612769 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(14948154545129392900548737 / 2000000000000000000000000), (37365704058282403821067419 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301 / 666)
  hi := (17 / 37)
  vmin := (109865 / 443556)
  damping := (109865 / 443556)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell376
