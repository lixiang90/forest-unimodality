import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell429
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (21)
  A := (4028289347803983261542271 / 25000000000000000000000000)
  B := (13910058979619064137289719 / 1000000000000000000000000000)
  C := (-20691792620915718664553751 / 1000000000000000000000000000)
  dδ := (7754257896617513384773801 / 500000000000000000000000000)
  dM := (37333305155411210599081251 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(13508021441933684703151641 / 100000000000000000000000000), (13849652627696675821766803 / 2500000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 35)
  hi := (37 / 140)
  vmin := (234 / 1225)
  damping := (374400000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell429
