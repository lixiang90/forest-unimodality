import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 71
  A := (23670427038135493091886019/500000000000000000000000000000)
  B := (10069058831455428293377707/100000000000000000000000000)
  C := (-52751439904134200808982769/100000000000000000000000000)
  dδ := (13563266922815558901405097/100000000000000000000000000)
  dM := (20914700728783619868011989/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(53664925286752840349890903/10000000000000000000000000), (44058215954810392434026767/50000000000000000000000000), (25710875046434704671582949/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301/666)
  hi := (17/37)
  vmin := (109865/443556)
  damping := (109865/443556)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell027
