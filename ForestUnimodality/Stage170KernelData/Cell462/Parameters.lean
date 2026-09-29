import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell462
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (97)
  A := (-22651839757563786881178203 / 10000000000000000000000000)
  B := (12038969293265562587880169 / 100000000000000000000000000)
  C := (-40375919823676803543932579 / 10000000000000000000000000000)
  dδ := (59134802814127959691425929 / 1000000000000000000000000000)
  dM := (12181342002789796556683211 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(2210614721781777092246557 / 4000000000000000000000000), (2539496429314449521541519 / 2500000000000000000000000), (93111276561240629234816879 / 1000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (1733 / 3648)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell462
