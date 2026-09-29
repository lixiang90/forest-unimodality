import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (-53737098753221791405110253/1000000000000000000000000000)
  B := (3878920331694125402111073/62500000000000000000000000)
  C := (-9773146749074155051340007/5000000000000000000000000000)
  dδ := (21745133982376339820685729/250000000000000000000000000)
  dM := (86801641025480401336889/80000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14940171442190881556655313/5000000000000000000000000), (66106194449355681896918213/10000000000000000000000000), (22131296630648193968227133/500000000000000000000000)]
  retention := ![(4/5), (3/5), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell050
