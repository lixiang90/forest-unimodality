import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (48319847492080357795884993/1000000000000000000000000000)
  B := (19042529386976213973126093/250000000000000000000000000)
  C := (15707403039837248507476497/2500000000000000000000000000)
  dδ := (11835774867873093130210549/100000000000000000000000000)
  dM := (8878892221237630636918037/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(17265596887406482462523627/2500000000000000000000000), (6406003261013339056262339/200000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557/44732)
  hi := (11791/22366)
  vmin := (124689825/500237956)
  damping := (124689825/500237956)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell144
