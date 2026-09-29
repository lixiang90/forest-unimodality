import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 85
  A := (-7026041773732827017084901/5000000000000000000000000)
  B := (46507397674685493904611633/500000000000000000000000000)
  C := (-18782170013760504830024889/10000000000000000000000000000)
  dδ := (31859812891057291694973941/500000000000000000000000000)
  dM := (5109697085374314239059057/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(21537893047821317082934911/2500000000000000000000000), (268178022344149269429181/80000000000000000000000), (11159173589957781302928197/250000000000000000000000), (13464441689164837967496169/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9287/19012)
  hi := (24/49)
  vmin := (90316075/361456144)
  damping := (90316075/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell054
