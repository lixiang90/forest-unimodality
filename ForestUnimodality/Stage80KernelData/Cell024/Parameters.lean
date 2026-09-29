import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-85125433851211023238647613/100000000000000000000000000)
  B := (2569623271078079751461587/20000000000000000000000000)
  C := (-30814982933398449294060129/100000000000000000000000000)
  dδ := (5540760494071171604613113/62500000000000000000000000)
  dM := (5585345368055540712232121/2500000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(8426410194187699431722649/2000000000000000000000000), (15996264907024196233464863/1000000000000000000000000)]
  retention := ![(1/2), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/51)
  hi := (67/153)
  vmin := (638/2601)
  damping := (638/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell024
