import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (1040046688796794399678447/5000000000000000000000000)
  B := (32926452239859849147052273/500000000000000000000000000)
  C := (37252767252900220729117109/5000000000000000000000000000)
  dδ := (5988533431082457281213749/50000000000000000000000000)
  dM := (8020202423317051264317623/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(73869017383566735190925101/10000000000000000000000000), (2500313764933802573864341/100000000000000000000000), (16764149587233971860911197/2500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95599/180624)
  hi := (11953/22578)
  vmin := (127000625/509766084)
  damping := (127000625/509766084)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell157
