import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (5841914556309727355483119/2000000000000000000000000)
  B := (-31257188305933519822943367/500000000000000000000000000)
  C := (-3442065774973023482841139/1000000000000000000000000000)
  dδ := (2591262789275303179969967/20000000000000000000000000)
  dM := (4734101194664567152691273/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7183102515123827913612331/1000000000000000000000000), (9285012447479341624045901/2500000000000000000000000), (13448869355175254725054401/500000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell057
