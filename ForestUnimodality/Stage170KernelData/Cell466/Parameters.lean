import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell466
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (95)
  A := (-19083173190495545290445989 / 10000000000000000000000000)
  B := (5321629070518619358809431 / 50000000000000000000000000)
  C := (-29400384494711706388769823 / 10000000000000000000000000000)
  dδ := (60044996585909601871655639 / 1000000000000000000000000000)
  dM := (5403816484544116290067439 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1533550314152033955394927 / 100000000000000000000000), (38849542290646837727763341 / 500000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23 / 48)
  hi := (2983 / 6208)
  vmin := (575 / 2304)
  damping := (575 / 2304)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell466
