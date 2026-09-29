import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (27)
  A := (1742618336038016069267087 / 10000000000000000000000000)
  B := (79629243437794976212540377 / 10000000000000000000000000000)
  C := (-771896288807162210196533 / 62500000000000000000000000)
  dδ := (5683934593659829056372379 / 625000000000000000000000000)
  dM := (12950684256101903152249427 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(34478588236647101439302787 / 100000000000000000000000)]
  retention := ![(9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell006
