import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (19943189871969338555857121/10000000000000000000000000)
  B := (-12363946993564016441080611/500000000000000000000000000)
  C := (-4686263289571907333409817/2500000000000000000000000000)
  dδ := (5303730344776088484470833/50000000000000000000000000)
  dM := (9896793902706257212414237/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(60437835703329998437993709/10000000000000000000000000), (689704518791105503083827/62500000000000000000000), (792442920585062182681213/40000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24/49)
  hi := (9529/19404)
  vmin := (600/2401)
  damping := (600/2401)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell066
