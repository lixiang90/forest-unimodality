import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (30)
  A := (17967329932963694739456173 / 100000000000000000000000000)
  B := (70304638249788133780304733 / 10000000000000000000000000000)
  C := (-11467428531503686545134357 / 1000000000000000000000000000)
  dδ := (78707651441198064196091977 / 10000000000000000000000000000)
  dM := (10550958245349928278189293 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(5505252065382265413973073 / 6250000000000000000000)]
  retention := ![(1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell015
