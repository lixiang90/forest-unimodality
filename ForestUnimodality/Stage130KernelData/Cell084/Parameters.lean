import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (-16532837195018791798162283/10000000000000000000000000)
  B := (12331916008969084214141887/125000000000000000000000000)
  C := (3128472488326695683663603/2000000000000000000000000000)
  dδ := (3018323496654015322682163/50000000000000000000000000)
  dM := (1290245893213778200468711/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(319102968842267908922139/31250000000000000000000), (1733162277332622736025769/625000000000000000000000), (38151784700062222555061453/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579/7004)
  hi := (5381/10506)
  vmin := (27577625/110376036)
  damping := (27577625/110376036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell084
