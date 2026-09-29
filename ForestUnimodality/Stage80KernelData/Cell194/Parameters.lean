import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell194
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 64
  A := (-7601113509783040150580291/25000000000000000000000000)
  B := (5734923519942879827082649/50000000000000000000000000)
  C := (24012821926854929777128689/50000000000000000000000000)
  dδ := (12901776880248808088147427/100000000000000000000000000)
  dM := (22611131845426432444845499/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(58354247530956460110473927/10000000000000000000000000), (8165178124008327653626793/2500000000000000000000000), (3815220868095841666445267/200000000000000000000000)]
  retention := ![(7/10), (1/5), (3/20)]
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
end ForestUnimodality.Stage80KernelData.Cell194
