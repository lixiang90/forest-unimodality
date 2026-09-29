import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-518590048921788706115521/312500000000000000000000)
  B := (5673515844555609283217379/50000000000000000000000000)
  C := (50141565076753085578031843/10000000000000000000000000000)
  dδ := (35082358685480589943761487/500000000000000000000000000)
  dM := (13527472230263860517029961/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(62139964616342444614360829/10000000000000000000000000), (36185935284003551970499757/5000000000000000000000000), (30412093882076021600369131/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95449/180624)
  hi := (47737/90312)
  vmin := (2032402775/8156257344)
  damping := (2032402775/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell152
