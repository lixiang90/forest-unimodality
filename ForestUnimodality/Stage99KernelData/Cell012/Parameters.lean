import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 25
  A := (1854667328152105040928177/12500000000000000000000000)
  B := (22588665735773720555368271/1000000000000000000000000000)
  C := (-12787673107340928949082759/250000000000000000000000000)
  dδ := (4774260394747729951969717/200000000000000000000000000)
  dM := (824345452306844196123381/4000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(801069511701315434271109/625000000000000000000000), (37585701846023944483476953/5000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/85)
  hi := (89/255)
  vmin := (1624/7225)
  damping := (2598400000000000000000000000000000000000000/28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell012
