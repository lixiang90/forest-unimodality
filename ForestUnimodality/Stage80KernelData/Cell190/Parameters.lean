import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell190
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 70
  A := (1871612989258058197151513/100000000000000000000000)
  B := (-28796388880295681333976177/100000000000000000000000000)
  C := (12136924958463135570951863/20000000000000000000000000)
  dδ := (3376890862546316762760057/20000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(20424783462173376591408669/1000000000000000000000000), (52597943069892014733568431/10000000000000000000000000), (1415282340467114208237831/125000000000000000000000), (12899100824118827191000491/1000000000000000000000000)]
  retention := ![(19/20), (3/5), (1/4), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1291/2376)
  hi := (2587/4752)
  vmin := (5600855/22581504)
  damping := (5600855/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell190
