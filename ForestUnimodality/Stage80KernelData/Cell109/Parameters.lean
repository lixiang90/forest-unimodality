import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-20041832021265786444530477/100000000000000000000000000)
  B := (10556146666230206698777749/100000000000000000000000000)
  C := (6246650338030759058716157/1000000000000000000000000000)
  dδ := (2597701055202585873615817/20000000000000000000000000)
  dM := (25522747244945001923732697/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(52805806274733351202144149/10000000000000000000000000), (5511663508621445828339347/500000000000000000000000), (968602281632450967663317/50000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell109
