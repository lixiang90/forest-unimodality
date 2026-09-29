import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell455
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (97)
  A := (-14650084515332843404422647 / 10000000000000000000000000)
  B := (44458047828326116568398163 / 500000000000000000000000000)
  C := (-26228656963201968377319417 / 100000000000000000000000000)
  dδ := (50136724490196148129594889 / 1000000000000000000000000000)
  dM := (41546337852714948805574191 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(16821395450425402628980009 / 1000000000000000000000000), (12984375185743333602772509 / 500000000000000000000000)]
  retention := ![(3 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301 / 666)
  hi := (17 / 37)
  vmin := (109865 / 443556)
  damping := (109865 / 443556)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell455
