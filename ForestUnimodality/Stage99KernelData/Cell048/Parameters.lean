import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 53
  A := (13868042645564444438122109/100000000000000000000000000)
  B := (55666942244917305693263643/1000000000000000000000000000)
  C := (-1559744085888805514589911/625000000000000000000000000)
  dδ := (88400448069635026437929071/1000000000000000000000000000)
  dM := (5229057264958512658142853/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8922951994746034509731203/2500000000000000000000000), (10277126755106031907871511/2000000000000000000000000), (13454480750861725013578507/500000000000000000000000), (1089754993233413848940927/62500000000000000000000)]
  retention := ![(4/5), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell048
