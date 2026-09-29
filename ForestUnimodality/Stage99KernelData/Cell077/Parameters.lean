import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-93856583387493624059061403/100000000000000000000000000)
  B := (56773601153579465045107/625000000000000000000000)
  C := (19058629057095255281140123/10000000000000000000000000000)
  dδ := (38437274262418011372410831/500000000000000000000000000)
  dM := (3118696357006677704129527/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(41385351363795432888537107/5000000000000000000000000), (894001075818063040134831/156250000000000000000000), (46987798322511245885380049/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26/51)
  hi := (3579/7004)
  vmin := (12258075/49056016)
  damping := (12258075/49056016)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell077
