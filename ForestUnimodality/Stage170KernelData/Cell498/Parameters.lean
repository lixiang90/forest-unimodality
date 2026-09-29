import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell498
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-17926963445140956976331381 / 10000000000000000000000000)
  B := (96914701881934656180206389 / 1000000000000000000000000000)
  C := (335580958254482093761073 / 125000000000000000000000000)
  dδ := (28675316976522546158490101 / 500000000000000000000000000)
  dM := (46847611634796788642950971 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(20847290020299800161751591 / 2500000000000000000000000), (45906865830539480555216869 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 207)
  hi := (7427 / 14352)
  vmin := (51431975 / 205979904)
  damping := (51431975 / 205979904)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell498
