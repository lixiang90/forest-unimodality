import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell433
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (23)
  A := (3588405422596626065612213 / 25000000000000000000000000)
  B := (7275660379450736223172491 / 500000000000000000000000000)
  C := (-23405070206673945359954203 / 1000000000000000000000000000)
  dδ := (15085847784273532720678013 / 1000000000000000000000000000)
  dM := (21096008278309714924127899 / 250000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7008165842109171927987177 / 5000000000000000000000000), (27286951922296682759849773 / 5000000000000000000000000)]
  retention := ![(3 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell433
