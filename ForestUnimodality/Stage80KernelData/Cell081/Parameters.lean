import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 38
  A := (873809794516896475862211/500000000000000000000000)
  B := (-18807769564461243594344353/10000000000000000000000000000)
  C := (27427025817323512477032693/500000000000000000000000000000)
  dδ := (11808190718894184811915693/100000000000000000000000000)
  dM := (83638779128256081005221567/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(29963389085455287563775073/5000000000000000000000000), (4204615589850971169028071/125000000000000000000000)]
  retention := ![(4/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (197/396)
  hi := (395/792)
  vmin := (39203/156816)
  damping := (39203/156816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell081
