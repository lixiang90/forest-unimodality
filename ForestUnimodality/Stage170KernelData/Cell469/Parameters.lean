import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell469
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (95)
  A := (-1316027388413389357513239 / 625000000000000000000000)
  B := (2313266749903552521594463 / 20000000000000000000000000)
  C := (-6774350372555782828082327 / 2500000000000000000000000000)
  dδ := (30068072950317239339090847 / 500000000000000000000000000)
  dM := (11874055727238562885778039 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(5444132045230742455999007 / 500000000000000000000000), (40974337841162736140177003 / 500000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8999 / 18624)
  hi := (47 / 97)
  vmin := (86615375 / 346853376)
  damping := (86615375 / 346853376)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell469
