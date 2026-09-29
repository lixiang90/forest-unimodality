import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell175
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 30
  A := (-2491555228346125993965643/20000000000000000000000000)
  B := (28820509638070236635432053/500000000000000000000000000)
  C := (6416686129310628095012703/50000000000000000000000000)
  dδ := (46981185246360780694008241/1000000000000000000000000000)
  dM := (84941356685392993206007439/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(5574359764630446578692613/2500000000000000000000000), (80997622944724998461651921/10000000000000000000000000), (2983178072369017108655953/2500000000000000000000000)]
  retention := ![(7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123/203)
  hi := (63/103)
  vmin := (2520/10609)
  damping := (2520/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell175
