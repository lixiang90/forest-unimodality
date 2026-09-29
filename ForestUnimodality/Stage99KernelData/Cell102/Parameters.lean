import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 51
  A := (-36040070444987778508050269/50000000000000000000000000)
  B := (19437623278765037149184991/200000000000000000000000000)
  C := (42669862672434933498211151/10000000000000000000000000000)
  dδ := (91428798838454353181681711/1000000000000000000000000000)
  dM := (1601977676088158853220933/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(36174336893655509861389419/5000000000000000000000000), (8591435879960133092936303/200000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22597/43472)
  hi := (11311/21736)
  vmin := (117917175/472453696)
  damping := (117917175/472453696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell102
