import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell434
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (24)
  A := (6575817877580234450007879 / 50000000000000000000000000)
  B := (7675834969138760864593163 / 500000000000000000000000000)
  C := (-6208298253978503274119749 / 250000000000000000000000000)
  dδ := (15349877848338740887745857 / 1000000000000000000000000000)
  dM := (5717814973379216351892073 / 62500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(5876301080353260042343777 / 2500000000000000000000000), (777955951975200787895659 / 156250000000000000000000)]
  retention := ![(1 / 2), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 126)
  hi := (19 / 63)
  vmin := (3293 / 15876)
  damping := (32930000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell434
