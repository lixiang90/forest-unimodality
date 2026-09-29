import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell340
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (29)
  A := (13707671125312505868265589 / 200000000000000000000000000)
  B := (1372295092027574735238371 / 125000000000000000000000000)
  C := (866158488685846682242353 / 50000000000000000000000000)
  dδ := (90927838835287190522027601 / 10000000000000000000000000000)
  dM := (50551208813743732481578441 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(404972957974509828460441 / 400000000000000000000000), (85104692378025905696858899 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35 / 52)
  hi := (53 / 78)
  vmin := (1325 / 6084)
  damping := (13250000000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell340
