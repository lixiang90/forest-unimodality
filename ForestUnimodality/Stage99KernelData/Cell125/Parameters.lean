import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 60
  A := (-61880266274883504284076707/100000000000000000000000000)
  B := (79977300197887152277687051/1000000000000000000000000000)
  C := (1808506880182234803459973/312500000000000000000000000)
  dδ := (39953785601114892578333837/500000000000000000000000000)
  dM := (11683994266257654009305567/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(16169471824891319400308021/10000000000000000000000000), (4102569445999049713158513/625000000000000000000000), (10225205738395935384232871/200000000000000000000000)]
  retention := ![(4/5), (7/10), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111/211)
  hi := (23557/44732)
  vmin := (498819475/2000951824)
  damping := (498819475/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell125
