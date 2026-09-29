import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (5224512308998835952600359/50000000000000000000000000)
  B := (1237984174542094235535461/62500000000000000000000000)
  C := (-923817298291859916731239/31250000000000000000000000)
  dδ := (4862141210653190583068639/250000000000000000000000000)
  dM := (15355083385219683682343383/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(47940615067479658284455013/100000000000000000000000000), (412435876519879514034983/80000000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell005
