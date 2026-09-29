import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 43
  A := (429208132986334050809063/250000000000000000000000)
  B := (-14515467434479054076312821/10000000000000000000000000000)
  C := (-17675567867738639291075309/5000000000000000000000000000)
  dδ := (11055965853396265696773071/100000000000000000000000000)
  dM := (70636143838462175752190841/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(64971064156092666053154971/10000000000000000000000000), (32304311096488187438069417/5000000000000000000000000), (31651849352079700850026711/1000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47/97)
  hi := (9237/19012)
  vmin := (2350/9409)
  damping := (2350/9409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell050
