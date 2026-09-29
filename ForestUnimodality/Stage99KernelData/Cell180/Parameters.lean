import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 23
  A := (36971431383155418549435467/100000000000000000000000000)
  B := (23947996719909526996961091/1000000000000000000000000000)
  C := (42419715187496542796452559/500000000000000000000000000)
  dδ := (1513559318290513544535969/40000000000000000000000000)
  dM := (16310570962366988871476703/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(7753556634265087454949139/5000000000000000000000000), (53575969545813195704653253/100000000000000000000000000), (32649235576925139667991971/5000000000000000000000000)]
  retention := ![(4/5), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236/371)
  hi := (9/14)
  vmin := (45/196)
  damping := (45/196)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell180
