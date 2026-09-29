import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell198
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 77
  A := (-3590137546921694902657407/2500000000000000000000000)
  B := (10220699172781871899573503/100000000000000000000000000)
  C := (50878359434232984376267339/10000000000000000000000000000)
  dδ := (68877461129235470482790049/1000000000000000000000000000)
  dM := (12128704744787043804526983/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5281388455672927584316767/500000000000000000000000), (1896800114679421389585201/1250000000000000000000000), (2989507624139587704803489/125000000000000000000000), (3950388735983943888641079/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8069/15194)
  hi := (12116/22791)
  vmin := (129338300/519429681)
  damping := (129338300/519429681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell198
