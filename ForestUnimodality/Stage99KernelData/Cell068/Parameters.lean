import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-65070783633237943121230273/100000000000000000000000000)
  B := (45546708697742417648601787/500000000000000000000000000)
  C := (16314613928057613992730901/25000000000000000000000000000)
  dδ := (90419467095795638678090711/1000000000000000000000000000)
  dM := (14892470002672792209197361/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(53581243715631847734925941/10000000000000000000000000), (13950424049855152386356849/5000000000000000000000000), (21055663049801385255932473/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51/101)
  hi := (10429/20604)
  vmin := (106115075/424524816)
  damping := (106115075/424524816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell068
