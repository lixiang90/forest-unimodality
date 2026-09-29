import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell459
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-18585258882931578361308311 / 10000000000000000000000000)
  B := (2058596670444861331805697 / 20000000000000000000000000)
  C := (-8485668663135497932770157 / 2000000000000000000000000000)
  dδ := (3697755811098442368933803 / 62500000000000000000000000)
  dM := (2571103304274109744437249 / 2500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16573083839334568079237897 / 2500000000000000000000000), (8945732931732699455551483 / 100000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1677 / 3572)
  hi := (841 / 1786)
  vmin := (3177915 / 12759184)
  damping := (3177915 / 12759184)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell459
