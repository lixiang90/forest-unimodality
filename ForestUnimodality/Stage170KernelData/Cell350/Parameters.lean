import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell350
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (22)
  A := (7126521037956993154693919 / 50000000000000000000000000)
  B := (99688331969096267027447 / 7812500000000000000000000)
  C := (-9198532784154367022977361 / 500000000000000000000000000)
  dδ := (6880566231387510132966323 / 500000000000000000000000000)
  dM := (30976503450822625933790133 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(4189366229395942164970279 / 1250000000000000000000000), (12865874767485083740581331 / 5000000000000000000000000)]
  retention := ![(1 / 2), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell350
