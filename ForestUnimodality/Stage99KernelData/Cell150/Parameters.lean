import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 112
  A := (2871357141803461660245489/25000000000000000000000000)
  B := (43282425081404979350097051/500000000000000000000000000)
  C := (12392769174814299848463861/20000000000000000000000000)
  dδ := (1695727323616133541683837/12500000000000000000000000)
  dM := (7292540500950863173110217/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(15586513163641058099528891/2500000000000000000000000), (36884699171705883635752343/10000000000000000000000000), (2010480019629891645926989/10000000000000000000000000), (1093945522162495365137147/50000000000000000000000), (19877265881074109188375587/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8069/15194)
  hi := (12116/22791)
  vmin := (129338300/519429681)
  damping := (129338300/519429681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell150
