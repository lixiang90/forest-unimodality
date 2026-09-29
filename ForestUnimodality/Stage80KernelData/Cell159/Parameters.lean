import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (916190680743828518330929/4000000000000000000000000)
  B := (64450586884269328580288061/1000000000000000000000000000)
  C := (18934584136763453390134293/2500000000000000000000000000)
  dδ := (1198528063469739418644977/10000000000000000000000000)
  dM := (15804396122959187172274387/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(74523765209057479808052449/10000000000000000000000000), (23635019961259480680837441/1000000000000000000000000), (80293822153286669163207989/10000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31883/60208)
  hi := (47837/90312)
  vmin := (2031876575/8156257344)
  damping := (2031876575/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell159
