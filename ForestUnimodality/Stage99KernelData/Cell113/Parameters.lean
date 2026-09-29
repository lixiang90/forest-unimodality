import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 60
  A := (-351917171927311600743149/781250000000000000000000)
  B := (8751019425883251046105471/125000000000000000000000000)
  C := (7889035915476495797182821/2000000000000000000000000000)
  dδ := (78181146866756090485495179/1000000000000000000000000000)
  dM := (2056527283192895617230933/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15356638685627050922022363/10000000000000000000000000), (4644844576896223209416803/625000000000000000000000), (2971944745659572717499941/200000000000000000000000), (8912045117782374958892433/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294/4389)
  hi := (1531/2926)
  vmin := (2135745/8561476)
  damping := (2135745/8561476)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell113
