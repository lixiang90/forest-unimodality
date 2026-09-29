import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 58
  A := (-95029075497483566191903037/100000000000000000000000000)
  B := (24721971573327995025382009/250000000000000000000000000)
  C := (-24376460937942587281490603/5000000000000000000000000000)
  dδ := (41514223712506362340413091/500000000000000000000000000)
  dM := (14506653297207859013712161/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5750650875469182077281971/1250000000000000000000000), (38573060447341913636876143/10000000000000000000000000), (48513739344676807263567753/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (869/1824)
  hi := (581/1216)
  vmin := (829895/3326976)
  damping := (829895/3326976)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell039
