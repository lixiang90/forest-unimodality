import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 15
  A := (48535396215767033787358287/1000000000000000000000000000)
  B := (28082383313233309773959689/1000000000000000000000000000)
  C := (-2140040321724540842845963/62500000000000000000000000)
  dδ := (273276070426027237192379/10000000000000000000000000)
  dM := (26087085850633331225376099/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(38122592883036480158887027/5000000000000000000000000000), (4795619353239775062291983/1250000000000000000000000)]
  retention := ![(9/20), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/4)
  hi := (9/35)
  vmin := (3/16)
  damping := (7500000000000000000000000000000000000000/98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell000
