import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 29
  A := (11732430044082862108822951/50000000000000000000000000)
  B := (1407867902940304052558651/62500000000000000000000000)
  C := (-69328438984389839649935539/1000000000000000000000000000)
  dδ := (27478444038777485869395889/1000000000000000000000000000)
  dM := (22212511743261722455683449/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(7042835395596728220724003/5000000000000000000000000), (47666031036832956502280467/5000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31/85)
  hi := (19/51)
  vmin := (1674/7225)
  damping := (1674/7225)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell015
