import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 124
  A := (12373718336203516244609091/100000000000000000000000000)
  B := (95344032184314420064197293/1000000000000000000000000000)
  C := (70452422340841081016549197/100000000000000000000000000)
  dδ := (3786793049664509414053981/25000000000000000000000000)
  dM := (2070619331542841517427439/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(17767797170393022643253289/2500000000000000000000000), (979431586525235431395231/250000000000000000000000), (13786195167695312946420927/500000000000000000000000), (9589203565343076718363591/500000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94503/178928)
  hi := (28/53)
  vmin := (700/2809)
  damping := (700/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell132
