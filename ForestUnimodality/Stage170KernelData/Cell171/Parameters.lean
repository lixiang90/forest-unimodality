import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell171
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (261)
  A := (-1662222379138997997429783 / 1000000000000000000000000)
  B := (47403838690922434073726777 / 1000000000000000000000000000)
  C := (90843647574550038213681 / 78125000000000000000000000)
  dδ := (7411686725882722648339751 / 250000000000000000000000000)
  dM := (5960246955726264313788279 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(48384983623010683118081943 / 1000000000000000000000000), (10546216002481786233602179 / 50000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell171
