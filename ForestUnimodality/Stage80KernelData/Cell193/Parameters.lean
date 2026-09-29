import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell193
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 63
  A := (-2057880296806673130447507/4000000000000000000000000)
  B := (14619739945067183883864459/100000000000000000000000000)
  C := (53778683061387277941634011/100000000000000000000000000)
  dδ := (15078587803059761984769693/100000000000000000000000000)
  dM := (15536414306803129469630731/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(7529726809663332964817073/2000000000000000000000000), (1556844975423499644051617/2000000000000000000000000), (5722511240243521868364951/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell193
