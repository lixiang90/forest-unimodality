import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-9562887966738759742924003/5000000000000000000000000)
  B := (13483425830745771056839999/100000000000000000000000000)
  C := (3151165854742848265214461/625000000000000000000000000)
  dδ := (74667167908422704680759807/1000000000000000000000000000)
  dM := (1080693493418778656318599/625000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15441069472307583865244851/1000000000000000000000000), (5157673763180383019744113/100000000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell132
