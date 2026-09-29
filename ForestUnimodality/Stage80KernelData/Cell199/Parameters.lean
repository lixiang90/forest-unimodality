import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell199
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 56
  A := (-9018337991131505415154379/50000000000000000000000000)
  B := (11325644147002443540284133/100000000000000000000000000)
  C := (11131755544424147552629023/25000000000000000000000000)
  dδ := (2571913606731526247273223/20000000000000000000000000)
  dM := (5931370205379351591423731/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(9507965200026946561706609/2000000000000000000000000), (200789628680073578559373/15625000000000000000000), (66691914634194962019364539/10000000000000000000000000)]
  retention := ![(7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99/179)
  hi := (5/9)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell199
