import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 50
  A := (-52638194124716757404058853/100000000000000000000000000)
  B := (21340604529296640368141169/250000000000000000000000000)
  C := (30584544888334268090968049/10000000000000000000000000000)
  dδ := (45694317024662443882387919/500000000000000000000000000)
  dM := (7149899451457436463236439/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13259407273868326626597991/2000000000000000000000000), (11852912340243157984787103/10000000000000000000000000), (18037788256159647204412977/500000000000000000000000), (54947264959145654117378399/10000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10787/21012)
  hi := (53/103)
  vmin := (2650/10609)
  damping := (2650/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell082
