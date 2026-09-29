import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 90
  A := (-10850680464874246544582093/10000000000000000000000000)
  B := (89348961055451078805411669/1000000000000000000000000000)
  C := (-30983974358378585378659409/100000000000000000000000000)
  dδ := (63280897306139227698196237/1000000000000000000000000000)
  dM := (3909289122792448771537277/4000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(64028569118678104743480617/10000000000000000000000000), (40793579938524970884827781/100000000000000000000000000), (15224754643783674268320283/1000000000000000000000000), (44644063272943625975131/2500000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301/666)
  hi := (17/37)
  vmin := (109865/443556)
  damping := (109865/443556)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell027
