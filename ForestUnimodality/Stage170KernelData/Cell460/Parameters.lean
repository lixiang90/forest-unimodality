import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell460
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-8364516839559882016530423 / 5000000000000000000000000)
  B := (9629280802915188286483783 / 100000000000000000000000000)
  C := (-21626466040287031962485731 / 5000000000000000000000000000)
  dδ := (59886355116757591932064031 / 1000000000000000000000000000)
  dM := (48369032510019871343512343 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(44328920011707806381195951 / 5000000000000000000000000), (43702880783918878648819373 / 500000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841 / 1786)
  hi := (1687 / 3572)
  vmin := (794745 / 3189796)
  damping := (794745 / 3189796)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell460
