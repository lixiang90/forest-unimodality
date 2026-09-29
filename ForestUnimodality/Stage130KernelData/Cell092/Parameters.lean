import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 90
  A := (-7921337043324634069563217/5000000000000000000000000)
  B := (96855713301457230235413931/1000000000000000000000000000)
  C := (23600209183694807225928347/10000000000000000000000000000)
  dδ := (30393491144328328712465037/500000000000000000000000000)
  dM := (10246622491358020178714439/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6105805277054672686176673/500000000000000000000000), (3807285253790887935565479/50000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21967/42642)
  hi := (10996/21321)
  vmin := (113533700/454585041)
  damping := (113533700/454585041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell092
