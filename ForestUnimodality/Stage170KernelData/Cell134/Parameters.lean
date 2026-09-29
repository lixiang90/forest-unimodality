import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (159)
  A := (-2434728477921989848997697 / 1250000000000000000000000)
  B := (74577254114787300265376757 / 1000000000000000000000000000)
  C := (-3781769586447865025280457 / 2000000000000000000000000000)
  dδ := (20233321790828370095871591 / 500000000000000000000000000)
  dM := (26447022257912911231969577 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(9148260508321618189597757 / 250000000000000000000000), (12042060942558751435171871 / 100000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23 / 48)
  hi := (47 / 97)
  vmin := (575 / 2304)
  damping := (575 / 2304)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell134
