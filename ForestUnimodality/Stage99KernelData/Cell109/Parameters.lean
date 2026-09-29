import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-12396284752121912192457387/25000000000000000000000000)
  B := (4659648844240562581831/64000000000000000000000)
  C := (18127982450221373587201379/5000000000000000000000000000)
  dδ := (79087752918160961201898829/1000000000000000000000000000)
  dM := (532154649240159749283563/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14778885463354312079786723/10000000000000000000000000), (37568545246095244038997407/5000000000000000000000000), (6882732802390722604002349/500000000000000000000000), (37671633253151085796162079/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell109
