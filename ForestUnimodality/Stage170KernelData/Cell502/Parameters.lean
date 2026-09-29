import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell502
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (102)
  A := (-244459813094008707317073 / 125000000000000000000000)
  B := (10442184941367421702196339 / 100000000000000000000000000)
  C := (28152340753385841215505891 / 10000000000000000000000000000)
  dδ := (14589668191263685526060101 / 250000000000000000000000000)
  dM := (5093031462620355902595759 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(30170559928109428327047681 / 5000000000000000000000000), (46122462534916436993626121 / 500000000000000000000000), (17097510011034326993240029 / 10000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (22597 / 43472)
  vmin := (471712375 / 1889814784)
  damping := (471712375 / 1889814784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell502
