import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell311
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (40)
  A := (-46681697167098825496101 / 3125000000000000000000000)
  B := (16050093445123217450465347 / 1000000000000000000000000000)
  C := (34325630631539018333686641 / 1000000000000000000000000000)
  dδ := (12011678391287970366074767 / 1000000000000000000000000000)
  dM := (862005827935624814465157 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(69491538504115646368575199 / 100000000000000000000000000), (1792269848185506830873237 / 125000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 53)
  hi := (467 / 742)
  vmin := (128425 / 550564)
  damping := (128425 / 550564)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell311
