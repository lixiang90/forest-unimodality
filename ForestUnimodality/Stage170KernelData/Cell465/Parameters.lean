import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell465
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (96)
  A := (-3947238830808619571826057 / 2000000000000000000000000)
  B := (5401524578636598267200597 / 50000000000000000000000000)
  C := (-14703447187443847033599953 / 5000000000000000000000000000)
  dδ := (59102551076529993845376509 / 1000000000000000000000000000)
  dM := (5441105435921156493681017 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1632425301425451058534577 / 125000000000000000000000), (80910826311552995093734353 / 1000000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (581 / 1216)
  hi := (23 / 48)
  vmin := (368935 / 1478656)
  damping := (368935 / 1478656)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell465
