import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell177
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 27
  A := (1598566669956029316921331/1000000000000000000000000)
  B := (-10448349351230356435449309/1000000000000000000000000000)
  C := (11655941146109817518894403/100000000000000000000000000)
  dδ := (46422923711053047657326687/1000000000000000000000000000)
  dM := (4792960201925779529315199/62500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(20943949716840937202988471/100000000000000000000000000), (19733946789960017387244307/10000000000000000000000000), (10193717801111548126868911/10000000000000000000000000), (18596801651072694117061701/5000000000000000000000000), (3030597673724279572660123/625000000000000000000000)]
  retention := ![(19/20), (9/10), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129/209)
  hi := (33/53)
  vmin := (660/2809)
  damping := (660/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell177
