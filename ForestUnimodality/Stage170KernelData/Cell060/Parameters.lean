import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (42)
  A := (8509584248730789835413191 / 50000000000000000000000000)
  B := (729053342443681715555337 / 62500000000000000000000000)
  C := (-659714819791700213258423 / 20000000000000000000000000)
  dδ := (5971694672019229807591323 / 500000000000000000000000000)
  dM := (27864617273422608744641929 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6992951069580027656513721 / 1000000000000000000000000), (43896901542951898278488443 / 5000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31 / 85)
  hi := (19 / 51)
  vmin := (1674 / 7225)
  damping := (1674 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell060
