import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (24690538466551367471346623/250000000000000000000000000)
  B := (19388205383635916806417399/1000000000000000000000000000)
  C := (-25298027243153879684012253/1000000000000000000000000000)
  dδ := (156468944580360374337763/7812500000000000000000000)
  dM := (6846795516266579212545651/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(15866381099251145037065669/25000000000000000000000000), (296110892904319598917251/78125000000000000000000)]
  retention := ![(1/2), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell000
