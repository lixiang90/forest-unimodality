import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (10000001947572297095234717/5000000000000000000000000)
  B := (-8055782067529004136785531/500000000000000000000000000)
  C := (-7292960452104574504972323/2000000000000000000000000000)
  dδ := (90948597480237247658863/800000000000000000000000)
  dM := (60165780686770233432608679/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(63650899559189531018432717/10000000000000000000000000), (28571312591859561180740457/10000000000000000000000000), (30667749907785299967599713/1000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell049
