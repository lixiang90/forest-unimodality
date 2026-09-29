import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 27
  A := (6904544302937240779716177/25000000000000000000000000)
  B := (17121073861636425944565687/500000000000000000000000000)
  C := (-11017387615511921306055143/100000000000000000000000000)
  dδ := (44084448552391873599187733/1000000000000000000000000000)
  dM := (49492029006645136580966327/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(11965679525692325402275173/10000000000000000000000000), (91959537301348550641932889/10000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/51)
  hi := (97/255)
  vmin := (608/2601)
  damping := (608/2601)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell016
