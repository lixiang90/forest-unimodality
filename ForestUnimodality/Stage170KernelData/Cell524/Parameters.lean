import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell524
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-4931345148508158140998603 / 2500000000000000000000000)
  B := (10556257238797220332493509 / 100000000000000000000000000)
  C := (43141030015306017220133583 / 10000000000000000000000000000)
  dδ := (28833078802516932948041273 / 500000000000000000000000000)
  dM := (10389248023392816996229859 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(88396293305997861722289599 / 10000000000000000000000000), (44567245277696727612237737 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (12116 / 22791)
  hi := (24257 / 45582)
  vmin := (517280525 / 2077718724)
  damping := (517280525 / 2077718724)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell524
