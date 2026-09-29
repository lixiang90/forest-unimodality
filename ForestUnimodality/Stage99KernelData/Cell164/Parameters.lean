import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 55
  A := (29610699540433141113737747/5000000000000000000000000)
  B := (-13166394300906911207782457/200000000000000000000000000)
  C := (13541236655804447797102341/50000000000000000000000000)
  dδ := (36159673286014742954463941/500000000000000000000000000)
  dM := (91644164128185250681006557/1000000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(13629579891147836079312583/2000000000000000000000000), (6939973068010051981957531/2000000000000000000000000), (12931834517952494056913793/10000000000000000000000000), (1136236866148644386598221/62500000000000000000000)]
  retention := ![(19/20), (7/10), (3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116/207)
  hi := (13/23)
  vmin := (130/529)
  damping := (130/529)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell164
