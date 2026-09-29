import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-2340625391128848460642331/1250000000000000000000000)
  B := (13224715976617407164894757/100000000000000000000000000)
  C := (28744366428533878882189967/5000000000000000000000000000)
  dδ := (596324689973193544645369/8000000000000000000000000)
  dM := (4229042249593637338780927/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(121380280436852283632021/7812500000000000000000), (10104408415640962459747243/200000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (15929/30104)
  hi := (95599/180624)
  vmin := (8128304975/32625029376)
  damping := (8128304975/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell166
