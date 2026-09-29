import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell354
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (24)
  A := (6804392029108505768775217 / 50000000000000000000000000)
  B := (1627269656536168944416243 / 125000000000000000000000000)
  C := (-10419180982374704261261833 / 500000000000000000000000000)
  dδ := (2666432228901502096696241 / 200000000000000000000000000)
  dM := (68089933793385434878178697 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(3754444653028757294954687 / 25000000000000000000000000), (34996842895085094049534291 / 5000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell354
