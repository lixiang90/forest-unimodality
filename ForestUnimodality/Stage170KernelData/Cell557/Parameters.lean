import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell557
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (20)
  A := (99105815104435900373403001 / 1000000000000000000000000000)
  B := (18737898516657788827721731 / 1000000000000000000000000000)
  C := (54989708935391470867593 / 2000000000000000000000000)
  dδ := (4304856973811538485563677 / 250000000000000000000000000)
  dM := (15209234578827379442793333 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15841132036981941944020491 / 2500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 156)
  hi := (9 / 13)
  vmin := (36 / 169)
  damping := (1440000000000000000000000000000000000000000 / 16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell557
