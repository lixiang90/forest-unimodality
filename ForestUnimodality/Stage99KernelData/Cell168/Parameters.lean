import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 46
  A := (-17674156501690191167597277/20000000000000000000000000)
  B := (5597231959242047333313863/50000000000000000000000000)
  C := (11134709536967207776925193/50000000000000000000000000)
  dδ := (32333636384619751646951613/500000000000000000000000000)
  dM := (170858637918699127027089/100000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(5452072241890081327753137/1250000000000000000000000), (7073213651460791062675071/500000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/187)
  hi := (27/47)
  vmin := (540/2209)
  damping := (540/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell168
