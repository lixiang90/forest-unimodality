import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell468
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (95)
  A := (-320976365710644435425003 / 156250000000000000000000)
  B := (2838665217252080499865663 / 25000000000000000000000000)
  C := (-28303250969100995915184171 / 10000000000000000000000000000)
  dδ := (30219726666368358636294289 / 500000000000000000000000000)
  dM := (232882630207192475174649 / 200000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(12078464130275676780001959 / 1000000000000000000000000), (5050605500058772179272637 / 62500000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4487 / 9312)
  hi := (8999 / 18624)
  vmin := (21649775 / 86713344)
  damping := (21649775 / 86713344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell468
