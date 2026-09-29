import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-3052950595772042732249929/2000000000000000000000000)
  B := (11000621782300865070247653/100000000000000000000000000)
  C := (6098008407079193518574023/2000000000000000000000000000)
  dδ := (71875581998891963086961709/1000000000000000000000000000)
  dM := (3361638641674406769409289/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9326716742433681872626039/2000000000000000000000000), (49696088146994403800249529/5000000000000000000000000), (57802132123623835013859207/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11153/21528)
  hi := (22331/43056)
  vmin := (462809975/1853819136)
  damping := (462809975/1853819136)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell101
