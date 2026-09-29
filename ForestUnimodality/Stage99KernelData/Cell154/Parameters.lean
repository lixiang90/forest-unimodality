import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 108
  A := (16241943609510559543451791/50000000000000000000000000)
  B := (76277930934462834233755757/1000000000000000000000000000)
  C := (59534403615257835973295641/100000000000000000000000000)
  dδ := (2632969771577223783154409/20000000000000000000000000)
  dM := (2661186689984057149316321/2000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(74274380551381540271904669/10000000000000000000000000), (34658271189698952596813797/10000000000000000000000000), (91829844325484373257495463/10000000000000000000000000), (15009256707244638562315231/500000000000000000000000)]
  retention := ![(4/5), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (48539/91164)
  hi := (97103/182328)
  vmin := (8275603175/33243499584)
  damping := (8275603175/33243499584)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell154
