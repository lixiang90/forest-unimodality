import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (38840302662038478430373/19531250000000000000000)
  B := (-7785453915215638856506253/500000000000000000000000000)
  C := (-17904134774618769235937643/5000000000000000000000000000)
  dδ := (11415950728188337115476259/100000000000000000000000000)
  dM := (30531887049563326491999349/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63389612289065961903133939/10000000000000000000000000), (5831454301368361292645659/1000000000000000000000000), (27707639285694451558583751/1000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell054
