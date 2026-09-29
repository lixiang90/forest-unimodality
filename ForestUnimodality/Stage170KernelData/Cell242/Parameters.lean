import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell242
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (86)
  A := (-2118435657262209574867029 / 4000000000000000000000000)
  B := (1454155852346892541238077 / 40000000000000000000000000)
  C := (12755186005802648940843369 / 100000000000000000000000000)
  dδ := (3096596204971839919051213 / 125000000000000000000000000)
  dM := (2971724847854875849011147 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(66399918531322805748118299 / 10000000000000000000000000), (30900306825076587102785197 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5 / 9)
  hi := (116 / 207)
  vmin := (10556 / 42849)
  damping := (10556 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell242
