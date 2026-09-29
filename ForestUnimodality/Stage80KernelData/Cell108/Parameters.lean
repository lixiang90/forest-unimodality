import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 43
  A := (-883940188861310628620771/6250000000000000000000000)
  B := (41270589461658076235739401/500000000000000000000000000)
  C := (3902235611834942944492477/1000000000000000000000000000)
  dδ := (702360023455261914954173/6250000000000000000000000)
  dM := (1079560327557581425389141/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(69795419513911314268739261/10000000000000000000000000), (197697950288893986581229/50000000000000000000000), (31816603244515302861827877/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11153/21528)
  hi := (22331/43056)
  vmin := (462809975/1853819136)
  damping := (462809975/1853819136)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell108
