import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (1852817890182015359101797 / 10000000000000000000000000)
  B := (39482114529732197788503001 / 5000000000000000000000000000)
  C := (-13123665839477126338064039 / 1000000000000000000000000000)
  dδ := (89734520056074049826344563 / 10000000000000000000000000000)
  dM := (13351002920861026942176211 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(328343061340164243944173 / 12500000000000000000000), (31063394263729890099057229 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 70)
  hi := (39 / 140)
  vmin := (969 / 4900)
  damping := (387600000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell014
