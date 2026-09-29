import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-5949424046995000719917357/5000000000000000000000000)
  B := (9475087623371972189723067/100000000000000000000000000)
  C := (1397781263990772234601101/500000000000000000000000000)
  dδ := (18208302044924604828901593/250000000000000000000000000)
  dM := (2329032186628948817436191/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(400188209484784565006521/40000000000000000000000), (10325162520158628898236941/12500000000000000000000000), (62909369306224284912332223/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell091
