import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 25
  A := (7067036450114559914759127/25000000000000000000000000)
  B := (970898472904979268835457/31250000000000000000000000)
  C := (-97282996382297370896452549/1000000000000000000000000000)
  dδ := (8159133967326641367900919/200000000000000000000000000)
  dM := (8664171143617695886041119/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(24499690576901372862650419/25000000000000000000000000), (61997308882543220032168563/1000000000000000000000000000), (84163533500158376199351551/10000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31/85)
  hi := (19/51)
  vmin := (1674/7225)
  damping := (1674/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell015
