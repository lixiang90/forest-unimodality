import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (10061390578733434509217659/50000000000000000000000000)
  B := (33068767551643014901419093/500000000000000000000000000)
  C := (67658351191863929513514719/10000000000000000000000000000)
  dδ := (2985974192991036613165079/25000000000000000000000000)
  dM := (8031558256824840313914393/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9187844653747301304491657/1250000000000000000000000), (11895079971948282704374833/1000000000000000000000000), (4960802246007415483575187/250000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28/53)
  hi := (95449/180624)
  vmin := (8129868575/32625029376)
  damping := (8129868575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell150
