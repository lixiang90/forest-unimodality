import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (132)
  A := (-18600654109011002701379311 / 10000000000000000000000000)
  B := (10457177622586071030763577 / 125000000000000000000000000)
  C := (-18901769465236325606753709 / 25000000000000000000000000000)
  dδ := (23858916194695944240633523 / 500000000000000000000000000)
  dM := (34159940044671072362572617 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(20270322760349774426913427 / 1000000000000000000000000), (10982266006713835793107137 / 100000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24 / 49)
  hi := (49 / 99)
  vmin := (600 / 2401)
  damping := (600 / 2401)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell143
