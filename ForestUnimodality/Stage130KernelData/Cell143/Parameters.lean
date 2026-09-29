import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-8508108324942160410842007/5000000000000000000000000)
  B := (2880789075639466484402007/25000000000000000000000000)
  C := (50470600403704334729892977/10000000000000000000000000000)
  dδ := (35041944831780344471461319/500000000000000000000000000)
  dM := (2742592510110467181327909/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10770692846056796554421453/2000000000000000000000000), (8626731650563904452155839/1000000000000000000000000), (30110636715898035475902361/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47239/89464)
  hi := (94503/178928)
  vmin := (7978415775/32015229184)
  damping := (7978415775/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell143
