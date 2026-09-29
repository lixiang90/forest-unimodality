import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell280
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (65)
  A := (-47058018524372158815083367 / 500000000000000000000000000)
  B := (16953404383466284810477731 / 1000000000000000000000000000)
  C := (54074564530703889131402207 / 1000000000000000000000000000)
  dδ := (6478193563745777636131429 / 500000000000000000000000000)
  dM := (40679765599708502367762297 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2807916970940891943087081 / 200000000000000000000000), (1610326436240241410047247 / 125000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 12)
  hi := (53 / 90)
  vmin := (1961 / 8100)
  damping := (1961 / 8100)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell280
