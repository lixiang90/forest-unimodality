import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell192
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-17178951732607518520978829/10000000000000000000000000)
  B := (2973045468209389863289971/25000000000000000000000000)
  C := (2124055702208085469329113/400000000000000000000000000)
  dδ := (1117997716500625021360249/15625000000000000000000000)
  dM := (14502120723317668635893307/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13001787022264079674016557/2500000000000000000000000), (10383364765467872903315083/1250000000000000000000000), (3669279155583974993959373/62500000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31933/60208)
  hi := (113/213)
  vmin := (11300/45369)
  damping := (11300/45369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell192
