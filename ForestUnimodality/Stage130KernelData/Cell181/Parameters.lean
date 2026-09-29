import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell181
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-1177751624446730053374921/625000000000000000000000)
  B := (13411095552448953904800533/100000000000000000000000000)
  C := (59688279392088074148947641/10000000000000000000000000000)
  dδ := (37861599040653198811057223/500000000000000000000000000)
  dM := (2159139990612079259939271/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15543278441370505404961477/1000000000000000000000000), (12625643647296719507266971/250000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95699/180624)
  hi := (7977/15052)
  vmin := (56437275/226562704)
  damping := (56437275/226562704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell181
