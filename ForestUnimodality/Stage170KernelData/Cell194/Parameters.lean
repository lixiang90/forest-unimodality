import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell194
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (169)
  A := (-3652816378701878421964011 / 2500000000000000000000000)
  B := (14749945809200810942218851 / 250000000000000000000000000)
  C := (13679609140481632095776021 / 5000000000000000000000000000)
  dδ := (40144288010492773510762277 / 1000000000000000000000000000)
  dM := (20091760830636093177088697 / 50000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16098229375829482989956887 / 1000000000000000000000000), (15140324570650736291099747 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111 / 211)
  hi := (28 / 53)
  vmin := (700 / 2809)
  damping := (700 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell194
