import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 92
  A := (-1489700962621563308232453/1000000000000000000000000)
  B := (45558168439640209235186319/500000000000000000000000000)
  C := (64134527251455462990709089/100000000000000000000000000000)
  dδ := (59619458914233230961698951/1000000000000000000000000000)
  dM := (94664573200995685495207077/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1517803701745328082139963/125000000000000000000000), (1381355729719471403527109/125000000000000000000000), (67258055471749031539729913/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407/808)
  hi := (51/101)
  vmin := (2550/10201)
  damping := (2550/10201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell074
