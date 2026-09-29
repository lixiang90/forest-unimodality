import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 72
  A := (-19452688250867823838063941/10000000000000000000000000)
  B := (13113278158861033095838877/100000000000000000000000000)
  C := (27318200688564399022939533/5000000000000000000000000000)
  dδ := (36176834496417994979644561/500000000000000000000000000)
  dM := (8080041774288316885552219/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3304891543586592206338537/200000000000000000000000), (53463393428114784455829067/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23607/44732)
  hi := (94453/178928)
  vmin := (7978917175/32015229184)
  damping := (7978917175/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell138
