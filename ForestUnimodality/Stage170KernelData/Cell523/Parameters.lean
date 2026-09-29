import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell523
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-10009474084265177157249127 / 5000000000000000000000000)
  B := (5369498548853923747259387 / 50000000000000000000000000)
  C := (331751033294412964571099 / 78125000000000000000000000)
  dδ := (58469403977822777263018139 / 1000000000000000000000000000)
  dM := (5305946513484522883419281 / 5000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(81099216604110431205754139 / 10000000000000000000000000), (22458492632996058802063999 / 250000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8069 / 15194)
  hi := (12116 / 22791)
  vmin := (129338300 / 519429681)
  damping := (129338300 / 519429681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell523
