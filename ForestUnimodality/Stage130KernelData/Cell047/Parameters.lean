import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-8744751254099128684416087/5000000000000000000000000)
  B := (2541036093636319104227539/20000000000000000000000000)
  C := (-5767792259111295671836217/2000000000000000000000000000)
  dδ := (76455620789642353418713583/1000000000000000000000000000)
  dM := (16292697771384564812968687/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2426395490955775358088431/200000000000000000000000), (5504551056974121081566409/100000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47/97)
  hi := (9237/19012)
  vmin := (2350/9409)
  damping := (2350/9409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell047
