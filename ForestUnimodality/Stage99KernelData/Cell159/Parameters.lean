import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-14911702139886416706815453/20000000000000000000000000)
  B := (11252552112436338405121461/100000000000000000000000000)
  C := (20061722528879388782740989/50000000000000000000000000)
  dδ := (24303545534603943761853273/250000000000000000000000000)
  dM := (17211154629470331971219377/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(69862325410422192462078783/10000000000000000000000000), (14910754759024142934720203/2500000000000000000000000), (19441805452001226228730957/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell159
