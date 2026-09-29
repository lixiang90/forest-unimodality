import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell538
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (57)
  A := (-33318581669583954340652099 / 50000000000000000000000000)
  B := (57586735677798796262383263 / 1000000000000000000000000000)
  C := (1646874264592422879016631 / 12500000000000000000000000)
  dδ := (16367011011169885215110753 / 500000000000000000000000000)
  dM := (53867035194071863791337451 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1185042790185077743458919 / 62500000000000000000000), (9186992996850527504193451 / 2000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 187)
  hi := (27 / 47)
  vmin := (540 / 2209)
  damping := (540 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell538
