import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (9762867700236145451953007/20000000000000000000000000)
  B := (405470657881983379509927/7812500000000000000000000)
  C := (32979655791897256184030951/5000000000000000000000000000)
  dδ := (11926891320578222877024643/100000000000000000000000000)
  dM := (14165079003904085079568187/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10447279737388925902052961/10000000000000000000000000), (31510450055869618779524899/5000000000000000000000000), (2001791401128224290317803/62500000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell148
