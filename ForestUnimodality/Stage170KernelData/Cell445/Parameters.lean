import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell445
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (40)
  A := (1344462942902601002126417 / 12500000000000000000000000)
  B := (19857877663153267883133779 / 1000000000000000000000000000)
  C := (-29379407188704735609530161 / 500000000000000000000000000)
  dδ := (3911545275220148359940353 / 200000000000000000000000000)
  dM := (1758415610278087155208919 / 12500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(31087686425390459454831671 / 10000000000000000000000000), (12449893616845532307024769 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 255)
  hi := (33 / 85)
  vmin := (15326 / 65025)
  damping := (15326 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell445
