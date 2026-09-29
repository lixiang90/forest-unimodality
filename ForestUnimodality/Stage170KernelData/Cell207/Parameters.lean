import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (282)
  A := (-19298893670747615980332057 / 10000000000000000000000000)
  B := (5071705530815282664258703 / 100000000000000000000000000)
  C := (1133961175761299131417581 / 500000000000000000000000000)
  dδ := (28677976550923856002839329 / 1000000000000000000000000000)
  dM := (24445859337234412175104969 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3473943971002440012085799 / 62500000000000000000000), (22446060704268691665674851 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113 / 213)
  hi := (57 / 107)
  vmin := (2850 / 11449)
  damping := (2850 / 11449)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell207
