import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 72
  A := (-47003748936606145669259149/50000000000000000000000000)
  B := (86766699578239903090093321/1000000000000000000000000000)
  C := (12302258636553040083150279/50000000000000000000000000)
  dδ := (3497615017021132692576213/62500000000000000000000000)
  dM := (98422249107781370480729777/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(68146986105751174989109131/10000000000000000000000000), (90600758134449854708236671/10000000000000000000000000), (15061924533965829198223219/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (99/179)
  hi := (5/9)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell217
