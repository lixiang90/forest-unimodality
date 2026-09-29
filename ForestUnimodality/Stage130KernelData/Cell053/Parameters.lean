import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 71
  A := (-30828682653448767375437/25000000000000000000000)
  B := (2001230828746364265313673/20000000000000000000000000)
  C := (-21967923772206071099388769/10000000000000000000000000000)
  dδ := (37512296303262693264457539/500000000000000000000000000)
  dM := (2541495162997431476320509/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3032568778353228466926339/500000000000000000000000), (4307478018062782965102997/1000000000000000000000000), (14830354829799691884772983/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell053
