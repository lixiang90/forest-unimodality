import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 79
  A := (-11130660600953096628273897/10000000000000000000000000)
  B := (88129223687146610033416039/1000000000000000000000000000)
  C := (-296764044496517290228077/62500000000000000000000000)
  dδ := (8734900801180498983167233/125000000000000000000000000)
  dM := (2622416265446028465699313/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(24536798867763089937454879/2500000000000000000000000), (29271757904217761137033449/500000000000000000000000), (47317888013350302145454407/5000000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841/1786)
  hi := (1687/3572)
  vmin := (794745/3189796)
  damping := (794745/3189796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell032
