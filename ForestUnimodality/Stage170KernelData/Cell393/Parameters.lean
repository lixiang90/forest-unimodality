import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell393
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (114)
  A := (-4848132903010943631194607 / 2500000000000000000000000)
  B := (95532967650781952517746731 / 1000000000000000000000000000)
  C := (34438738631766339752526829 / 10000000000000000000000000000)
  dδ := (52401385158178777345927557 / 1000000000000000000000000000)
  dM := (86392182199718117567577291 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(17552192911254170581969447 / 1000000000000000000000000), (18891921283249283192162693 / 200000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111 / 211)
  hi := (28 / 53)
  vmin := (700 / 2809)
  damping := (700 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell393
