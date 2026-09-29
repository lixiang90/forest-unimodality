import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 89
  A := (-14851169612202767444841811/10000000000000000000000000)
  B := (11697556106375588472201521/125000000000000000000000000)
  C := (8019415108467292012742189/2500000000000000000000000000)
  dδ := (7728947453622709608256347/125000000000000000000000000)
  dM := (49900181885461475893295269/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(105663113643227599136587/7812500000000000000000), (36965695339427163901291351/500000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583/8778)
  hi := (2294/4389)
  vmin := (4805930/19263321)
  damping := (4805930/19263321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell116
