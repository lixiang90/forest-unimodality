import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell253
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (89)
  A := (-1041633249175056914026527 / 3125000000000000000000000)
  B := (2708929621260749553285363 / 125000000000000000000000000)
  C := (72907607401394000645744597 / 1000000000000000000000000000)
  dδ := (7126468516615231015010057 / 500000000000000000000000000)
  dM := (19994061528307073582512443 / 200000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(16621526032396435113014377 / 1000000000000000000000000), (21653652957345972396296929 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 23)
  hi := (21 / 37)
  vmin := (336 / 1369)
  damping := (336 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell253
