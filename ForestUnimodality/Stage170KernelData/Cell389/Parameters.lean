import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell389
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (115)
  A := (-6990456650665414447543 / 3906250000000000000000)
  B := (89329715038716950292752017 / 1000000000000000000000000000)
  C := (1217147339395163252798171 / 500000000000000000000000000)
  dδ := (53382273040549939324694861 / 1000000000000000000000000000)
  dM := (9954785531596356356037053 / 12500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(18133470566993842965075601 / 1000000000000000000000000), (95026034552074037264901563 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 207)
  hi := (27 / 52)
  vmin := (675 / 2704)
  damping := (675 / 2704)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell389
