import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-1910486518211539837253099/1250000000000000000000000)
  B := (19192529021745030615164751/200000000000000000000000000)
  C := (42024479385043113713327223/10000000000000000000000000000)
  dδ := (12604620432863053447469781/200000000000000000000000000)
  dM := (10264266770558070230451309/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6389540981854942458539881/500000000000000000000000), (8206075189772322753256617/20000000000000000000000000), (12466642281862979402262681/500000000000000000000000), (1207253246107012856214169/25000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557/44732)
  hi := (11791/22366)
  vmin := (124689825/500237956)
  damping := (124689825/500237956)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell134
