import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 19
  A := (2374398820709102886539199/20000000000000000000000000)
  B := (16568692523298109153806479/500000000000000000000000000)
  C := (16360923858056559271334507/250000000000000000000000000)
  dδ := (34646765271573114197689591/1000000000000000000000000000)
  dM := (8725924494163740663399409/20000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(65027664644586256059710649/10000000000000000000000000)]
  retention := ![(3/5)]
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
end ForestUnimodality.Stage99KernelData.Cell183
