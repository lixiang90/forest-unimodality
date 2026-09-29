import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell261
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (75)
  A := (-174041742500611010946443 / 625000000000000000000000)
  B := (24462151700452926250672903 / 1000000000000000000000000000)
  C := (15991460104120053253851097 / 200000000000000000000000000)
  dδ := (4285359894498677255092467 / 250000000000000000000000000)
  dM := (13385636834905716196011949 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1055705037947483493354639 / 125000000000000000000000), (23436868684449578381645551 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 93)
  hi := (107 / 187)
  vmin := (8560 / 34969)
  damping := (8560 / 34969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell261
