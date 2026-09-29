import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-7430172459756162145438907/5000000000000000000000000)
  B := (2718327096025130798495617/25000000000000000000000000)
  C := (8529193024432618923033611/2500000000000000000000000000)
  dδ := (36122297869616570853423809/500000000000000000000000000)
  dM := (13359067717898152026501091/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(16073496363298549471920751/2500000000000000000000000), (63008761057677578065749913/10000000000000000000000000), (11942973587686424252751749/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell107
