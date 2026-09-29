import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (-82363054260029923128172413/1000000000000000000000000000)
  B := (85844108477297217940638063/1000000000000000000000000000)
  C := (41157949730641109342688111/5000000000000000000000000000)
  dδ := (1463613401376286440869201/12500000000000000000000000)
  dM := (2561209843838432452696463/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2218904536334104804495837/400000000000000000000000), (4118687253282198312831497/250000000000000000000000), (11786779109611934757140261/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2326/4431)
  hi := (4657/8862)
  vmin := (19582685/78535044)
  damping := (19582685/78535044)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell136
