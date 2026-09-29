import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell238
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (13109142902898958006119301/100000000000000000000000000)
  B := (24248981357247741119653739/1000000000000000000000000000)
  C := (1962141942582580067533371/40000000000000000000000000)
  dδ := (4993310372305637817591517/200000000000000000000000000)
  dM := (757863134431864102940387/3125000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(33554307631986803883705761/10000000000000000000000000), (42095870733726847845446173/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (83/126)
  hi := (2/3)
  vmin := (2/9)
  damping := (80000000000000000000000000000000000000000/888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell238
