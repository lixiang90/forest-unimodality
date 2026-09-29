import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 66
  A := (-13987156331839527029003989/25000000000000000000000000)
  B := (49143340731852461211737193/500000000000000000000000000)
  C := (7060301320404031022448521/20000000000000000000000000)
  dδ := (44430877305436496105262023/500000000000000000000000000)
  dM := (14901129882103490882638841/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(63021429385152689661708791/10000000000000000000000000), (64455525836527334249126397/10000000000000000000000000), (3182774550448365857846511/200000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/89)
  hi := (99/179)
  vmin := (7920/32041)
  damping := (7920/32041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell161
