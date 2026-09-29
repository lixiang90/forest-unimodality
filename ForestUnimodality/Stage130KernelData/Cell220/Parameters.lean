import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell220
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 59
  A := (-67033351126395517404432667/100000000000000000000000000)
  B := (72240879782350525539769137/1000000000000000000000000000)
  C := (18871275512122015483029713/100000000000000000000000000)
  dδ := (9362524812108337368687927/200000000000000000000000000)
  dM := (16280744726865968661361217/20000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(54984148690853826835223117/10000000000000000000000000), (10096865332209548071773497/1000000000000000000000000), (45755224106505867354144357/5000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/23)
  hi := (21/37)
  vmin := (336/1369)
  damping := (336/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell220
