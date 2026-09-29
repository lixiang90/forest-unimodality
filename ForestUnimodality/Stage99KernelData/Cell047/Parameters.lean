import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 54
  A := (11150050083295474290423499/20000000000000000000000000)
  B := (7875404883536049616132857/200000000000000000000000000)
  C := (-27013932933418055570840011/10000000000000000000000000000)
  dδ := (45010674221315993825953683/500000000000000000000000000)
  dM := (87605428692433967314406873/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(51739514389150853546084363/10000000000000000000000000), (21600489993446823078215857/5000000000000000000000000), (26513595498091792279637957/1000000000000000000000000), (1846254761331474725238877/100000000000000000000000)]
  retention := ![(4/5), (1/2), (1/10), (1/20)]
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
end ForestUnimodality.Stage99KernelData.Cell047
