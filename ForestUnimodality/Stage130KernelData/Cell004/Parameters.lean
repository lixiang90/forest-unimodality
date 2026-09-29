import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 21
  A := (144635901716544844628487/1000000000000000000000000)
  B := (14895300263861033923662447/1000000000000000000000000000)
  C := (-4735356609463665933379417/200000000000000000000000000)
  dδ := (7908518103685159214566447/500000000000000000000000000)
  dM := (11184469379291465108397681/125000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(10840060370943092049600409/10000000000000000000000000), (25105730226837734697653559/5000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39/140)
  hi := (2/7)
  vmin := (3939/19600)
  damping := (393900000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell004
