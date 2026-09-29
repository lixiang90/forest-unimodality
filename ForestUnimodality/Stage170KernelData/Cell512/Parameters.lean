import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell512
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-5577424529380007159318211 / 2500000000000000000000000)
  B := (5782744541264594334561977 / 50000000000000000000000000)
  C := (7960487572763297325906251 / 2000000000000000000000000000)
  dδ := (725217026022435644339037 / 12500000000000000000000000)
  dM := (11353671128032129244989079 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1474600922228258115254107 / 500000000000000000000000), (95765801225496062443198753 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326 / 4431)
  hi := (4657 / 8862)
  vmin := (19582685 / 78535044)
  damping := (19582685 / 78535044)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell512
