import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (39)
  A := (19744809811577552661532309 / 100000000000000000000000000)
  B := (99899530872014710713990837 / 10000000000000000000000000000)
  C := (-25568350503960762115651661 / 1000000000000000000000000000)
  dδ := (10999900203569262097103021 / 1000000000000000000000000000)
  dM := (42769593603078648064858003 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(19147698967840420802843937 / 2500000000000000000000000), (7641968707693225226762479 / 1250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 85)
  hi := (89 / 255)
  vmin := (1624 / 7225)
  damping := (2598400000000000000000000000000000000000000 / 28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell051
