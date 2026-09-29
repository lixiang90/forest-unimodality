import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell458
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-3277896138804857397701653 / 2000000000000000000000000)
  B := (46672592751178673675660491 / 500000000000000000000000000)
  C := (-5384331073841481770173023 / 1250000000000000000000000000)
  dδ := (2900360274057905973776883 / 50000000000000000000000000)
  dM := (92777079962016908553507077 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(92084677178362817073775659 / 10000000000000000000000000), (8709889447213919311252539 / 100000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 47)
  hi := (1677 / 3572)
  vmin := (550 / 2209)
  damping := (550 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell458
