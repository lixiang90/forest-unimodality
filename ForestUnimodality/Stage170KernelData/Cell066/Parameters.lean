import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (50)
  A := (10235485262802016482197587 / 50000000000000000000000000)
  B := (23437693653910233147763531 / 2500000000000000000000000000)
  C := (-15136513870736926015703183 / 500000000000000000000000000)
  dδ := (10079108145245960909131 / 1000000000000000000000000)
  dM := (7489740337433057183833679 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(25078574884138808975819757 / 10000000000000000000000000), (1663521641348900104162567 / 200000000000000000000000), (83585097173722910923743257 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 51)
  hi := (97 / 255)
  vmin := (608 / 2601)
  damping := (608 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell066
