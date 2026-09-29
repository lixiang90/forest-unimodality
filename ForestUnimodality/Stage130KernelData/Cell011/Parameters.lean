import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 27
  A := (3639890464536034353670857/20000000000000000000000000)
  B := (16605885651088940491160173/1000000000000000000000000000)
  C := (-7647872027286650720157013/200000000000000000000000000)
  dδ := (2283634141024826896826383/125000000000000000000000000)
  dM := (2959139796912370139712889/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(65523427895761088279869/80000000000000000000000), (53632950165218478133510871/10000000000000000000000000), (15774614653128411490001781/5000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/3)
  hi := (29/85)
  vmin := (2/9)
  damping := (80000000000000000000000000000000000000000/888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell011
