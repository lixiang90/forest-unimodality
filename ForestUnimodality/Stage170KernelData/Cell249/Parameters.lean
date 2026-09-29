import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell249
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (70)
  A := (-11629669643355036473320041 / 25000000000000000000000000)
  B := (631830311933864155644891 / 15625000000000000000000000)
  C := (1228634402176933260175673 / 10000000000000000000000000)
  dδ := (5435674427243677997445559 / 200000000000000000000000000)
  dM := (3803320253425003185819217 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(27287797165993668002670347 / 10000000000000000000000000), (10611599607578836579335757 / 2500000000000000000000000), (22846144450976638040629041 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 23)
  hi := (21 / 37)
  vmin := (336 / 1369)
  damping := (336 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell249
