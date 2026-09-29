import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell209
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 45
  A := (-2215571243335014408586403/2000000000000000000000000)
  B := (7437512543747611115652063/50000000000000000000000000)
  C := (28481326045426563764451089/100000000000000000000000000)
  dδ := (84782273043831776759837737/1000000000000000000000000000)
  dM := (13227186014727015765657381/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(23908805530918275650265059/5000000000000000000000000), (6600163599062889296931189/500000000000000000000000)]
  retention := ![(2/5), (7/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21/37)
  hi := (53/93)
  vmin := (2120/8649)
  damping := (2120/8649)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell209
