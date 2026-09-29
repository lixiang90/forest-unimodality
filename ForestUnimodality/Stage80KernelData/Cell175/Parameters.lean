import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell175
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 88
  A := (-28001106568419358410437781/100000000000000000000000000)
  B := (13135295016397349754377899/100000000000000000000000000)
  C := (34875674473566181665873387/50000000000000000000000000)
  dδ := (4345889277922517640595501/25000000000000000000000000)
  dM := (27088695236633314814000961/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(22788859740127089814620831/2500000000000000000000000), (15427300652389771329353607/500000000000000000000000)]
  retention := ![(7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell175
