import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-17060746447136202930039417/10000000000000000000000000)
  B := (5951592399623264334485029/50000000000000000000000000)
  C := (1746184621430521902163413/400000000000000000000000000)
  dδ := (35472529564691789027985891/500000000000000000000000000)
  dM := (1464585900510425794940339/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(41225181779226671707760943/10000000000000000000000000), (18808342551455663027581977/2000000000000000000000000), (57700666304057733668742003/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531/2926)
  hi := (11/21)
  vmin := (110/441)
  damping := (110/441)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell119
