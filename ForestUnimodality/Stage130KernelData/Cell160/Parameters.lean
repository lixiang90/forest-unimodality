import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-4666636848720278454827337/2500000000000000000000000)
  B := (2625110318470316173034007/20000000000000000000000000)
  C := (55762747020045499643514653/10000000000000000000000000000)
  dδ := (73877351490768294883793033/1000000000000000000000000000)
  dM := (16724640023901358575758591/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15540277537585089007166061/1000000000000000000000000), (50524776646136068336545577/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23881/45156)
  hi := (95549/180624)
  vmin := (8128831175/32625029376)
  damping := (8128831175/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell160
