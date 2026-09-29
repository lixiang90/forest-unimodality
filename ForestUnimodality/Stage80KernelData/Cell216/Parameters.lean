import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (5534559583543080118488433/500000000000000000000000)
  B := (-673391092663628731962433/4000000000000000000000000)
  C := (1623682435492976305901891/6250000000000000000000000)
  dδ := (3520160534692852172256039/40000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(490441207178246614262207/40000000000000000000000), (97480239451348733581426131/10000000000000000000000000), (10732388995785431262675047/2500000000000000000000000)]
  retention := ![(19/20), (3/10), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653/1128)
  hi := (7/12)
  vmin := (35/144)
  damping := (35/144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell216
