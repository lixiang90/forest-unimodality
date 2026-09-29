import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (-1378251298853578755920779/6250000000000000000000000)
  B := (10007908552057985518413119/100000000000000000000000000)
  C := (940926305787297823221213/156250000000000000000000000)
  dδ := (12372009661545950442995689/100000000000000000000000000)
  dM := (11454388125335444956892639/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11243325144870745191383321/2000000000000000000000000), (25419245547962479037096273/5000000000000000000000000), (13478139970948566528363699/500000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/207)
  hi := (7427/14352)
  vmin := (51431975/205979904)
  damping := (51431975/205979904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell105
