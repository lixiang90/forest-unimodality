import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-16637607370959425667678033/10000000000000000000000000)
  B := (1275534000182133170797627/12500000000000000000000000)
  C := (24164508939414921194488439/5000000000000000000000000000)
  dδ := (31432372563741761695155219/500000000000000000000000000)
  dM := (2738177800182668123092633/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1135616620818415967164583/100000000000000000000000), (13742261129519854900848941/5000000000000000000000000), (11565496581562005218302147/1000000000000000000000000), (7576012800489291265648717/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47837/90312)
  hi := (95699/180624)
  vmin := (8127237575/32625029376)
  damping := (8127237575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell180
