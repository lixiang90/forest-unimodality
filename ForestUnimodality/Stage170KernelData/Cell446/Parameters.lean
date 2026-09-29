import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell446
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (42)
  A := (24945942182100060984240031 / 500000000000000000000000000)
  B := (4132120146694077261750877 / 200000000000000000000000000)
  C := (-61774572726979698478189107 / 1000000000000000000000000000)
  dδ := (768107161035435498375179 / 40000000000000000000000000)
  dM := (453063040030345170431237 / 3125000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(15958736347482398443275997 / 5000000000000000000000000), (3353117870187153126693147 / 250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 85)
  hi := (101 / 255)
  vmin := (1716 / 7225)
  damping := (1716 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell446
