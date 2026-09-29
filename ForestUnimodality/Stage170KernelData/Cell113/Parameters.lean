import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (137)
  A := (-7850518340791984750381971 / 10000000000000000000000000)
  B := (7587491535244754795042077 / 250000000000000000000000000)
  C := (-13235067616785717303784509 / 100000000000000000000000000)
  dδ := (9914360103104721474998051 / 500000000000000000000000000)
  dM := (7115246092461147934139093 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10228920972086434915127029 / 1250000000000000000000000), (40302723865412396264673589 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell113
