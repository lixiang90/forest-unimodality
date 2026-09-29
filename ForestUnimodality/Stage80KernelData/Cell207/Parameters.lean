import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell207
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 42
  A := (-48943200540774153328271723/50000000000000000000000000)
  B := (8584787885611236402105817/50000000000000000000000000)
  C := (36731573439619469301220533/100000000000000000000000000)
  dδ := (12040937749548429047674603/100000000000000000000000000)
  dM := (4493820898097326366031623/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8175672454469257388609549/500000000000000000000000), (1075744157864028799354017/3125000000000000000000000)]
  retention := ![(3/10), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21/37)
  hi := (53/93)
  vmin := (2120/8649)
  damping := (2120/8649)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell207
