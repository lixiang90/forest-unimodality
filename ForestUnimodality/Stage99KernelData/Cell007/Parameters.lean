import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 20
  A := (9057357193920049927005067/125000000000000000000000000)
  B := (21094037531892369935482279/1000000000000000000000000000)
  C := (-8012683208858038114152933/250000000000000000000000000)
  dδ := (19276225132699376790812451/1000000000000000000000000000)
  dM := (8540539815958006714200629/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(19730453206364692575469633/100000000000000000000000000), (808166165824745874601831/4000000000000000000000000), (58122720165395858060719547/10000000000000000000000000)]
  retention := ![(3/5), (1/2), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/63)
  hi := (13/42)
  vmin := (836/3969)
  damping := (33440000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell007
