import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell335
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (28)
  A := (14452663788230349086738613 / 250000000000000000000000000)
  B := (6052208278298646174087061 / 500000000000000000000000000)
  C := (4899874494403460255254057 / 250000000000000000000000000)
  dδ := (12348449229935990010403879 / 1250000000000000000000000000)
  dM := (2469648540588066567419423 / 40000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(44603317364122867239029091 / 500000000000000000000000000), (92724690963965272771929449 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 3)
  hi := (35 / 52)
  vmin := (595 / 2704)
  damping := (1487500000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell335
