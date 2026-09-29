import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (6196474790831955015590893/50000000000000000000000000)
  B := (7614323533917045222496611/500000000000000000000000000)
  C := (-1478943779491951162133323/62500000000000000000000000)
  dδ := (1915103942839629317523853/125000000000000000000000000)
  dM := (92201174581196823306673827/1000000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(91964794075929390260171203/100000000000000000000000000), (56256250835856373981869183/10000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/7)
  hi := (37/126)
  vmin := (10/49)
  damping := (400000000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell005
